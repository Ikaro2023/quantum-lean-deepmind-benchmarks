"""Compare the serialized kernel expression bytes in independent Lean processes."""
import argparse
import hashlib
import json
from lean_tools import BIN, LIB, REPO, PROJECT, ROOT, digest, record

SUFFIXES=("Cells","Cells_nonempty","Cells_mem_grid","Qubits","Circuit","Program","_correctness","RelCost","_rel_cost")
PUBLIC=["groverFind"+side+s for side in ("Any","All") for s in SUFFIXES]
MODELS=["groverSetMarkingOracle","groverParallelMarkingOracle","groverTargetSets","decodeTargets",
        "AvgOracleCostBound","groverHarmonicSqrtSum","vanillaFindAnyCost","vanillaFindAllCost",
        "groverGrid","groverFindAnyProgram","groverFindAllProgram"]
FROZEN="QuantumComputationSpecs.Algorithms.Grover"
PROG=r"""
import Lean
open Lean Elab Command
private partial def anonymize : Expr → Expr
  | .app f x => .app (anonymize f) (anonymize x)
  | .lam _ t b bi => .lam .anonymous (anonymize t) (anonymize b) bi
  | .forallE _ t b bi => .forallE .anonymous (anonymize t) (anonymize b) bi
  | .letE _ t v b d => .letE .anonymous (anonymize t) (anonymize v) (anonymize b) d
  | .mdata _ e => anonymize e
  | .proj i k e => .proj i k (anonymize e)
  | e => e
"""


def inspect(mod,raw=False):
    program=PROG
    for kind, names, sel in [("type",PUBLIC,"i.type"),("value",MODELS,"i.value?.get!")]:
        for name in names:
            program+=f'\nrun_cmd\n  let i ← getConstInfo ``QuantumComputation.Specs.{name}\n'
            expression=sel if raw else "(anonymize "+sel+")"
            program+=f'  liftIO <| IO.println ("{kind}/{name} " ++ (Lean.toJson (reprStr {expression})).compress)\n'
    rc,log=record(("raw_interface_" if raw else "interface_")+mod,[BIN/"lean.exe","-j1","--stdin"],stdin=("import "+mod+"\n"+program).encode())
    if rc:
        raise RuntimeError(f"{mod} inspection failed: {log}")
    records=dict(line.split(b" ",1) for line in log.read_bytes().splitlines() if line.startswith((b"type/",b"value/")))
    if len(records)!=len(PUBLIC)+len(MODELS): raise RuntimeError(f"Incomplete inspection: {log}")
    return records,log


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("module")
    parser.add_argument("--raw",action="store_true",help="Retain all binder names and expression metadata")
    args=parser.parse_args()
    mod=args.module
    path="QuantumComputationSpecs/Algorithms/Grover"
    frozen=ROOT/"formal-quantum-computation"/(path+".lean")
    work=REPO/(path+".lean")
    if frozen.read_bytes()!=work.read_bytes(): raise ValueError("Frozen source disagreement")
    ref,l1=inspect(FROZEN,args.raw)
    actual,l2=inspect(mod,args.raw)
    rows={field.decode():dict(equal=ref[field]==actual[field],
            frozen_sha256=hashlib.sha256(ref[field]).hexdigest(),
            candidate_sha256=hashlib.sha256(actual[field]).hexdigest()) for field in ref}
    output=dict(target=mod,reference=FROZEN,reference_source_sha256=digest(frozen),
                reference_olean_sha256=digest(LIB/(path+".olean")),frozen_log=l1.name,candidate_log=l2.name,
                compared_declaration_types=len(PUBLIC),compared_model_and_program_bodies=len(MODELS),
                equal=all(row["equal"] for row in rows.values()), rows=rows)
    output["binder_names_and_metadata_retained"]=args.raw
    (PROJECT/(("raw_interface_" if args.raw else "interface_")+mod+".json")).write_text(json.dumps(output,indent=2)+"\n",encoding="utf-8")
    print(mod,output["equal"],len(rows))
    return 0 if output["equal"] else 1

if __name__=="__main__":
    raise SystemExit(main())
