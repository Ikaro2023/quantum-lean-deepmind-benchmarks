# Track 1 (`Track1THC`) — Partial Foundations Only (0/7 Definition Holes + 0/2 Public Theorems Filled)

> **Important Epistemic Notice:** The open benchmark `QuantumComputationSpecs/Primitives/THCFactorization.lean` (`THCFactorization.json`) is **NOT solved**. Exactly **0 of the 7 frozen candidate definition holes** (`thcBlockAncillas`, `thcScratchAncillas`, `thcCatalystQubits`, `thcCandidateAlpha`, `thcCandidateOffset`, `thcCandidateProgram`, `thcTCost`) and **0 of the 2 frozen public theorems** (`thc_correctness`, `thc_t_cost`) are filled, and no formally verified T-counts for FeMoco (Reiher/Li) exist in this release.

> **Audit Disclosure:** All 9 modules in this directory were authored by Claude Code (`sonnet`, high effort). They were **not** independently audited by a second agent; their soundness rests on Lean `4.35.0` elaboration and the machine-checked `leanchecker.exe` replay archived in `receipts/track1_thc_partial/track1_thc_9modules_leanchecker.json` (`9/9` modules exit `0`, `0 sorry`, standard axioms `[propext, Classical.choice, Quot.sound]` only).

### Mathematical / LCU Layer (6 modules, 1,306 lines)
1. `Alias.lean` (147 lines) — Exact integer Walker–Vose alias decomposition (`alias_exists`).
2. `JWAlgebra.lean` (567 lines) — Jordan–Wigner canonical anticommutation relations (`jwAnnihilate_anticomm_conj`, absent from upstream `JordanWignerOrbitalAlgebra.lean`), orbital number idempotence, and reflection involutivity.
3. `Centering.lean` (203 lines) — Exact centered THC Hamiltonian decomposition (`thc_centering`) matching the frozen 1-norm `lamRep` without an extra factor of 2.
4. `LCUa.lean` (33 lines) — Existence of a unitary matrix with prescribed real unit first column (`exists_unitary_first_col`).
5. `LCU.lean` (255 lines) — Abstract qubitized block-encoding existence (`lcu_blockEncoding` producing `IsQubitizedBlockEncodingUnitary`).
6. `Select.lean` (101 lines) — Involutive `swapSelect` construction (`lcu_of_involutive_family`) handling non-Hermitian products of non-commuting reflections.

### Circuit-Algebra Layer (3 modules, 650 lines)
7. `CleanOps.lean` (397 lines) — Clean and catalytic `DynamicCircuit` sequential composition (`realizesClean_seq`, `realizesClean_of_clean_action`, `realizesClean_lift`, `realizesCatalytic_seq`), additive `TOFF = 0` / `T`-count `CostBound` algebra, and lifted clean Jones-AND (`exists_jonesToffoli_on_target`, `T <= 4`, `TOFF = 0`).
8. `CatalyticRot.lean` (168 lines) — Exact eigenvector kickback of cyclic shift on frozen `phaseGradientState b` (`cycShift_phaseGradient`, `controlledAdd_kick`) and bridge to `RealizesCatalyticSubroutine` (`catalytic_of_net_action`).
9. `CliffordGadgets.lean` (85 lines) — Clean single-qubit gates, `CZ` gadget (`TOFF = 0, T = 0`), and clean Toffoli chains (`exists_toffoli_chain`, `T <= 4 * L.length`).

Remaining work required to close `THCFactorization.json` (estimated ~5,000–10,000 additional lines): concrete Clifford+`T`+measurement ripple-carry/Gidney adder circuit, register-level catalytic net-action proof, general-$N$ Givens cascade circuit, QROM + comparator + controlled-swap Alias PREP circuit, SELECT circuit, and closed-form `thcTCost` bound.
