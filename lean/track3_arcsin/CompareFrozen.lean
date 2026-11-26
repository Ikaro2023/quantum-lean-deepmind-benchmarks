import Lean

open Lean

def challenge : Name := `QuantumComputationSpecs.Primitives.Arcsin
def solution : Name := `QuantumComputationDiscoveries.Primitives.Arcsin

def targets : Array Name := #[
  `QuantumComputation.Specs.arcsin_correctness,
  `QuantumComputation.Specs.arcsin_k25_const_cost,
  `QuantumComputation.Specs.arcsinAncillas,
  `QuantumComputation.Specs.arcsinProgram,
  `QuantumComputation.Specs.arcsinK25ConstCost]

/-- Compare the declarations reachable within the frozen module. Hole bodies
are supplied by the solution. Compare every reachable type, every other
definition body, and the families and types of inductive constructors. -/
def compare (spec impl : Environment) : IO Unit := do
  let mut todo := targets
  let mut seen : NameSet := {}
  while let some n := todo.back? do
    todo := todo.pop
    if seen.contains n then continue
    unless (spec.getModuleIdxFor? n).map (spec.header.moduleNames[·]!) == some challenge do
      continue
    seen := seen.insert n
    let some a := spec.find? n | throw <| IO.userError s!"Frozen declaration missing {n}"
    let some b := impl.find? n | throw <| IO.userError s!"Candidate declaration missing {n}"
    unless a.type == b.type && a.levelParams == b.levelParams do
      throw <| IO.userError s!"Type mismatch {n}"
    todo := todo ++ a.type.getUsedConstants
    if targets.contains n then
      unless a.isTheorem == b.isTheorem && a.isDefinition == b.isDefinition do
        throw <| IO.userError s!"Declaration kind mismatch {n}"
      IO.println s!"TYPE {n}"
    else
      if let .inductInfo ai := a then
        let .inductInfo bi := b | throw <| IO.userError s!"Expected inductive {n}"
        unless ai.ctors == bi.ctors && ai.numParams == bi.numParams && ai.numIndices == bi.numIndices do
          throw <| IO.userError s!"Inductive mismatch {n}"
        todo := todo ++ ai.ctors.toArray
      unless a.value? == b.value? do throw <| IO.userError s!"Body mismatch {n}"
      if let some v := a.value? then todo := todo ++ v.getUsedConstants
      IO.println s!"FROZEN {n}"
  unless targets.all seen.contains do throw <| IO.userError "Missing challenge targets"
  IO.println s!"PASS {seen.size} challenge declarations"

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let frozen ← importModules #[{module := challenge}] {}
  let candidate ← importModules #[{module := solution}] {}
  compare frozen candidate
