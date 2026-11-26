"""Compare the elaborated kernel types of the frozen and submitted declarations.

Both modules define the same public names. Inspect them in fresh Lean processes.
Encode the full Expr tree, erasing only binder names and expression metadata.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
repo = root / "work_repo"
lib = repo / ".lake/build/lib/lean"
assert (lib / "QuantumComputationSpecs/Algorithms/Grover.olean").is_file()
out = root / "track2_grover/receipts"
binary = root / ".elan/toolchains/leanprover--lean4---v4.35.0/bin/lean.exe"
parser = argparse.ArgumentParser()
parser.add_argument("side", choices=["Any", "All"])
side = parser.parse_args().side
public = ["groverFind"+side+x for x in ("Cells","Cells_nonempty","Cells_mem_grid","Qubits",
          "Circuit","Program","_correctness","RelCost","_rel_cost")]
models = ["groverSetMarkingOracle","groverParallelMarkingOracle","groverTargetSets",
          "AvgOracleCostBound","vanillaFind"+side+"Cost","groverGrid","groverFind"+side+"Program"]
if side == "All":
    models += ["decodeTargets","groverHarmonicSqrtSum"]
program = r"""
import Lean
open Lean Elab Command
private partial def eraseBinderNames : Expr → Expr
  | .app f x => .app (eraseBinderNames f) (eraseBinderNames x)
  | .lam _ t b bi => .lam .anonymous (eraseBinderNames t) (eraseBinderNames b) bi
  | .forallE _ t b bi => .forallE .anonymous (eraseBinderNames t) (eraseBinderNames b) bi
  | .letE _ t v b d => .letE .anonymous (eraseBinderNames t) (eraseBinderNames v) (eraseBinderNames b) d
  | .mdata _ e => eraseBinderNames e
  | .proj i k e => .proj i k (eraseBinderNames e)
  | e => e
"""
for kind, names in (("type",public),("value",models)):
    for name in names:
        selector = "i.type" if kind=="type" else "i.value?.get!"
        program += f'''
run_cmd
  let i ← getConstInfo ``QuantumComputation.Specs.{name}
  liftIO <| IO.println ("{kind}/{name} " ++ (Lean.toJson (reprStr (eraseBinderNames {selector}))).compress)
'''
env = dict(os.environ, ELAN_HOME=str(root/".elan"),
           LEAN_PATH=os.pathsep.join(map(str,[lib,*sorted((repo/".lake/packages").glob("*/.lake/build/lib/lean")),repo])))
def inspect(module):
    result = subprocess.run([str(binary),"-j1","--stdin"], input=("import "+module+"\n"+program).encode(),
                            capture_output=True, cwd=repo, env=env)
    contents = (result.stdout+result.stderr).decode("utf8")
    if result.returncode:
        raise RuntimeError(contents[-5000:])
    return dict(line.split(" ",1) for line in contents.splitlines() if line.startswith(("type/","value/")))
control = inspect("QuantumComputationSpecs.Algorithms.Grover")
test = inspect("Track2Grover."+("TighterFindAny" if side=="Any" else "FindAll"))
assert len(control) == len(public)+len(models) and set(control)==set(test)
matches = {}
for field, expected in control.items():
    got = test[field]
    matches[field] = {"equal":got==expected,
                      "expected_sha256":hashlib.sha256(expected.encode()).hexdigest(),
                      "actual_sha256":hashlib.sha256(got.encode()).hexdigest()}
    if got!=expected:
        path = out / f"interface_{side}_{field.replace('/','_')}_difference.json"
        path.write_text(json.dumps({"frozen":expected,"submitted":got},indent=2),encoding="utf8")
(out / f"interface_{side}.json").write_text(json.dumps(matches,indent=2),encoding="utf8")
for field, item in matches.items():
    print(field, "identical" if item["equal"] else "different", flush=True)
raise SystemExit(0 if all(x["equal"] for x in matches.values()) else 1)
