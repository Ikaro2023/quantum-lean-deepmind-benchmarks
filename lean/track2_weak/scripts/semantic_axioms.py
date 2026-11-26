"""Audit the public target's actual imported environment and the full private local kernel objects."""
import json
from pathlib import Path

from lean_tools import BIN, LEAN, PROJECT, digest, record

TARGET = "Track2Weak.FindAllWeak"
BASE = "QuantumComputation.Specs."
SIDES = ("Any", "All")
SUFFIX = ("Cells", "Cells_nonempty", "Cells_mem_grid", "Qubits", "Circuit", "Program",
          "_correctness", "RelCost", "_rel_cost")
PUBLIC = [BASE + "groverFind" + side + suffix for side in SIDES for suffix in SUFFIX]
TARGET_THM = BASE + "groverFindAllRelCost_target"
MODELS = [BASE + name for name in (
    "Grover.Var", "groverSetMarkingOracle", "groverParallelMarkingOracle", "groverTargetSets",
    "decodeTargets", "AvgOracleCostBound", "groverHarmonicSqrtSum", "vanillaFindAnyCost",
    "vanillaFindAllCost", "groverGrid")]
ALLOWED = {"Classical.choice", "Quot.sound", "propext"}
CHECK = r"""
open Lean Elab Command

private def origin? (env : Environment) (d : Name) : Option Name := do
  let i ← env.getModuleIdxFor? d
  return (← env.header.modules[i.toNat]?).module

run_cmd do
  let env ← getEnv
  let emit := fun (j : Json) ↦ liftIO (IO.println ("AXAUDIT " ++ j.compress))
  for n in NAMES do
    let ci ← getConstInfo n
    let axs ← collectAxioms n
    emit (Json.mkObj [("kind", "entry"), ("name", toJson n.toString),
      ("module", toJson ((origin? env n).map Name.toString)),
      ("direct_axiom", toJson (ci matches .axiomInfo _)),
      ("axioms", toJson (axs.map Name.toString))])
  let imported := env.header.modules.map (·.module)
  emit (Json.mkObj [("kind", "imported"), ("names", toJson (imported.map Name.toString))])
  let locals : Array Name := LOCAL_MODULES
  for m in locals do
    let path ← liftIO (findOLean m)
    let parts ← liftIO (readModuleDataParts #[path, OLeanLevel.server.adjustFileName path,
                                                OLeanLevel.private.adjustFileName path])
    let some (info, _) := parts.back? | throwError "missing full kernel object"
    let direct := info.constants.filterMap fun c ↦ if c matches .axiomInfo _ then some c.name.toString else none
    let inClosure := imported.contains m
    let mut visible := 0
    if inClosure then
      for c in info.constants do
        if env.contains c.name && origin? env c.name == some m then
          visible := visible + 1
          let axs ← collectAxioms c.name
          emit (Json.mkObj [("kind", "reachable"), ("name", toJson c.name.toString),
            ("module", toJson m.toString), ("axioms", toJson (axs.map Name.toString))])
    emit (Json.mkObj [("kind", "object"), ("module", toJson m.toString),
      ("full_declarations", toJson info.constants.size), ("visible_declarations", toJson visible),
      ("direct_axiom_names", toJson direct), ("in_target_environment", toJson inClosure)])
"""


def run():
    sources = sorted((LEAN / "Track2Weak").glob("*.lean"))
    modules = ["Track2Weak." + src.stem for src in sources]
    exported = PUBLIC + [TARGET_THM]
    names = exported + MODELS
    program = "import " + TARGET + "\nimport Lean\n" + "\n".join("#print axioms " + n for n in exported) + "\n"
    checks = CHECK.replace("LOCAL_MODULES", "#[" + ",".join("`" + m for m in modules) + "]")
    program += checks.replace("NAMES", "#[" + ",".join("`" + n for n in names) + "]")
    request = PROJECT / "semantic_axioms.stdin.txt"
    request.write_text(program, encoding="utf-8")
    rc, log = record("final_semantic_axioms", [BIN / "lean.exe", "-j1", "--stdin"], stdin=program.encode())
    if rc:
        raise RuntimeError(str(log) + "\n" + "\n".join(line for line in log.read_text(encoding="utf-8").splitlines() if ": error" in line))
    rows = [json.loads(line.removeprefix("AXAUDIT ")) for line in log.read_text(encoding="utf-8").splitlines()
            if line.startswith("AXAUDIT ")]
    entities = {r["name"]: r for r in rows if r["kind"] == "entry"}
    imports = next(r["names"] for r in rows if r["kind"] == "imported")
    objects = [r for r in rows if r["kind"] == "object"]
    declarations = [r for r in rows if r["kind"] == "reachable"]
    assert set(entities) == set(names)
    assert {r["module"] for r in objects} == set(modules)
    for o in objects:
        name = o["module"].split(".")[-1]
        stem = LEAN / "Track2Weak" / name
        o["source_sha256"] = digest(stem.with_suffix(".lean"))
        o["private_object_sha256"] = digest(stem.with_suffix(".olean.private"))
    outside = sorted({ax for r in [*entities.values(), *declarations] for ax in r["axioms"]} - ALLOWED)
    direct = [ax for o in objects for ax in o["direct_axiom_names"]]
    frozen = "QuantumComputationSpecs.Algorithms.Grover"
    assert not outside and not direct and frozen not in imports
    assert not any(r["direct_axiom"] for r in entities.values())
    assert {r["module"] for r in objects if r["in_target_environment"]} == {m for m in imports if m.startswith("Track2Weak.")}
    summary = {
        "target": TARGET, "request": request.name, "request_sha256": digest(request),
        "receipt": str(log.with_suffix(".json").relative_to(PROJECT)),
        "raw_log": str(log.relative_to(PROJECT)), "raw_log_sha256": digest(log),
        "receipt_sha256": digest(log.with_suffix(".json")),
        "permitted_axioms": sorted(ALLOWED), "unexpected_transitive_axioms": outside,
        "local_direct_axioms": direct, "local_modules_on_disk": len(objects),
        "local_modules_in_actual_target_environment": sum(o["in_target_environment"] for o in objects),
        "total_full_private_declarations_in_all_local_objects": sum(o["full_declarations"] for o in objects),
        "transitive_axioms_checked_for_visible_owned_declarations": len(declarations),
        "per_module_private_inventories": objects,
        "public_interface_declarations": [entities[n] for n in PUBLIC],
        "target_theorem": entities[TARGET_THM], "model_declarations": [entities[n] for n in MODELS],
        "frozen_stub_module_in_target_environment": frozen in imports,
        "imported_modules_under_Track2Grover": [m for m in imports if m.startswith("Track2Grover.")],
        "metadata": "Full private kernel objects count direct declarations, including unexported helpers and out-of-closure controls. Lean.collectAxioms is additionally queried on every project-owned declaration visible in the actual imported target environment. The raw log lists each per-declaration result and all imported module names; it contains the requested literal #print axioms outputs.",
    }
    out = PROJECT / "final_semantic_axioms.json"
    out.write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
    print("PASS", len(PUBLIC), "public declarations + target theorem;", len(objects), "local module objects;",
          summary["total_full_private_declarations_in_all_local_objects"], "declarations;",
          len(declarations), "owned transitive checks;", len(outside), "unexpected transitive axioms;",
          len(direct), "direct axioms;", "SHA-256", digest(out))


if __name__ == "__main__":
    run()