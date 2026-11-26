# TRACK 1 ROUND 3 (THCFactorization): circuit-half report (Claude Code, `sonnet`, high effort)

Date: 2026-11-25. Toolchain: Lean 4.35.0 (isolated `.elan`), Mathlib/physlib as in `work_repo`.

## 0. Bottom line (read first)

**`THCFactorization.json` is still NOT solved. 0 of the 7 frozen holes are filled, and `thc_correctness` and `thc_t_cost` are not proved.**
There is still no `thcTCost` or `thcTotalLogicalQubits`, so there are no proved numbers for Reiher (N=54, M=350) or Li (N=76, M=450). `Track1THC\THCSolution.lean` was not created, because there is nothing honest to put in it.

Round 3 added three verified modules (650 lines, 0 `sorry`, standard axioms only, `leanchecker.exe` exit 0 on each). They are the **first part of the circuit half**:

| Mission item | Status | What exists |
|---|---|---|
| 1. `CleanOps.lean` clean composition algebra | **Partly done.** | Sequencing, identity, congruence, chains, catalytic sequencing, sub-register lifting, `TOFF`/`T` cost algebra, clean Jones-AND (Toffoli) on an arbitrary target. |
| 2. `CatalyticRot.lean` catalytic β-rotation | **Algebraic core only (about 40%).** | Exact phase-gradient eigenvector theorem, controlled-adder kickback, bridge to `RealizesCatalyticSubroutine`. **No adder circuit, so no `T`-count `O(β)` theorem.** |
| 3. `GivensCircuit.lean` | **Not started.** | None. |
| 4. `AliasCircuit.lean` / `THCSolution.lean` | **Not started.** | None. |

The cost of each missing piece is itemized in §4, and the remaining glue is in §5.

## 1. New verified modules

All three live in `track1_thc\Track1THC\` and are mirrored as `.lean` (copy only) to `work_repo\Track1THC\`. `work_repo\lakefile.toml` was not touched. The oleans are in `track1_thc\_build\Track1THC\`.

| File | Lines | `sorry` | Role |
|---|---|---|---|
| `CleanOps.lean` | 397 | 0 | Clean/catalytic composition algebra and cost algebra |
| `CatalyticRot.lean` | 168 | 0 | Exact phase-gradient kickback and catalytic bridge |
| `CliffordGadgets.lean` | 85 | 0 | `CZ` gadget, Toffoli chains on a common target |

### 1.1 `CleanOps.lean`

Everything is proved from the frozen library `QuantumComputation.*` plus the frozen spec's `RealizesCatalyticSubroutine`. Nothing imports `discoveries_ref`.

* `triple_seq`: Hoare-triple sequencing for `QProg.qSeq`, derived from `expect_wp`. The library has no such rule.
* `proj_mul_embed`, `embed_adj_mul_proj`, `restrict_idem`, `restrict_qAssign_restrict`: a target-embedded unitary commutes with the clean-ancilla projector of a disjoint register. This lets it absorb an inner clean restriction. It is the key lemma behind sequencing.
* `realizesClean_skip`, `realizesClean_seq`: identity, and sequential composition `U₂ * U₁` on the same target and ancilla.
* `realizesClean_qAssign`: any target-embedded unitary assignment realizes its unitary.
* **`realizesClean_of_clean_action`:** any unitary assignment `W` realizes `U` as soon as `W · P₀ = (embed U) · P₀`, where `P₀` projects onto the clean ancilla subspace. No condition on dirty inputs is needed: unitarity forces `W` to preserve the dirty subspace, and the proof shows `P₀ W = W P₀ = (embed U) P₀`. This is what lets a catalytic net unitary `V⁻¹ · Add · V`, which is not a target-embedded unitary, still be a clean realization.
* `realizesClean_congr`: programs with the same `wp` are interchangeable.
* `realizesClean_of_embed_eq`, `realizesClean_lift`: transfer along an equal embedding, and **disjoint register lifting**. A subroutine that realizes `U` on the sub-register `rT.compose sub` realizes `sub.embedUnitary U` on the whole target `rT`.
* `chainU`, `chainP`, `realizesClean_chain`: sequential composition of an arbitrary list of clean subroutines.
* `realizesCatalytic_skip`, `realizesCatalytic_seq`, `realizesCatalytic_of_clean`: catalytic identity and sequencing. The proof uses `V⁻¹ ; V` cancellation at the `wp` level (`wp_conj_cancel`, `wp_conj_cancel'`).
* `CostBound P t` (that is, `count TOFF = 0 ∧ count T ≤ t`), closed under identity, measure, `seq` (additive `t + u`), `qIf` (`max`), `mono` and list chains (`CostBound.dchain`, `compile_dchain`).
* **`CostBound.jonesToffoli`:** cost `(TOFF = 0, T ≤ 4)`.
* **`exists_jonesToffoli_on_target`:** Jones' measurement-assisted Toffoli placed on any three wires `sub` of a larger target register `rT`, with one clean ancilla outside `rT`. It realizes `rT.embed (sub.embed toffoli)` cleanly with cost `(0, 4)`. It reuses the library's `DynamicCircuit.realizesCleanSubroutine_jonesToffoli`; the new content is the lifting.

### 1.2 `CatalyticRot.lean`

* **`cycShift_phaseGradient`:** the cyclic shift by `j` on `Fin (2^b)` has the frozen `phaseGradientState b` as an *exact* eigenvector with eigenvalue `exp(2π i j / 2^b)`. The proof uses a modular-exponential lemma, `exp_two_pi_sub_mod`, and the `Fin` subtraction formula. This is the exact-phase claim of the mission: no approximation.
* `ctrlAdd` and **`controlledAdd_kick`:** the controlled adder `|t⟩|c⟩ ↦ |t⟩|c + t⟩` sends `|t⟩ ⊗ φ_b` to `exp(2π i t/2^b) · (|t⟩ ⊗ φ_b)`. A catalyst in the frozen phase-gradient state therefore receives the exact rotation `diag(exp(2π i t/2^β))` on the target, and is returned intact.
* **`catalytic_of_net_action`:** a bridge to `RealizesCatalyticSubroutine`. A single unitary assignment `Wp` is a catalytic realization of `U` on `rT` as soon as, for every `V` with first column `phaseGradientState b`, the net unitary `V⁻¹ · Wp · V` acts on the clean subspace as the target-embedded `U`.

### 1.3 `CliffordGadgets.lean`

* `realizesClean_gate1`: any single-qubit primitive gate on wire `t` realizes its unitary.
* `czCircuit c t` is `H t ; CNOT c t ; H t` (the library's own `CZ`). **`realizesClean_cz`** shows it realizes `czUnitary := H₂ · CNOT · H₂` on `pair c t` with any disjoint clean ancilla. **`czCircuit_cost`** shows `TOFF = 0` and `T = 0`.
* **`exists_toffoli_chain`:** for any list `L` of triples `sub` of a common target `rT`, one shared clean ancilla wire, there is a circuit that realizes the product of the Toffoli unitaries on `rT` with `TOFF = 0` and `T ≤ 4 · L.length`.

**Caveat on `czUnitary`.** It is defined as the product `H₂ · CNOT · H₂`, as the library does. I did **not** prove `czUnitary = diag(1,1,1,−1)`. That is a standard fact, but the `4×4` entry computation through `embedMatrix` was not done.

## 2. Verification evidence

* `lean.exe` (via `lc.sh <M> -o`): `CleanOps`, `CatalyticRot` and `CliffordGadgets` all **exit 0**. Only linter notes remain (unused `variable`, `DecidableEq` on a few lemmas, a `simp` cosmetic).
* **`leanchecker.exe Track1THC.<M>`: exit 0 on `CleanOps`, `CatalyticRot` and `CliffordGadgets`.** Negative control: `leanchecker.exe Track1THC.DoesNotExist` exits 1.
* `grep -c sorry Track1THC/*.lean`: **0 in all 9 files.** There are no custom `axiom` declarations.
* `#print axioms` (file `track1_thc\scratch\Axioms3.lean`, exit 0) for 27 new declarations. Every one depends only on subsets of `[propext, Classical.choice, Quot.sound]`:
  * Three cost lemmas (`CostBound.seq`, `.qIf`, `.dchain`) use only `[propext]`.
  * `CostBound.jonesToffoli` and `czCircuit_cost` use `[propext, Quot.sound]`.
  * All the others use all three.
* **`count PrimitiveGate.TOFF = 0`:** proved as the first component of `CostBound` for `jonesToffoli`, for `czCircuit`, and for every chain built from them (`exists_toffoli_chain`). It is **not** proved for any `thcCandidateProgram`, because that program does not exist yet.
* Read-only boundaries: no file under `formal-quantum-computation\`, `discoveries_ref\`, `work_repo\QuantumComputation\`, `work_repo\QuantumComputationSpecs\`, `work_repo\lakefile.toml` or `first_league_v2_20261125\` is newer than Round 2's `Select.lean`.

## 3. A finding about the reference modules

`discoveries_ref\...\P450GroundEnergy\Solution\PhaseGradAdder.lean` (321 lines) has a docstring promising Gidney ripple-carry adders (`addMod2PowDyn`, `ctrlAdd13Into14Dyn`, …, "`4 * (b - 1)` `T`"). In this copy, **none is defined**: `addMod2PowDyn` and `addCarryChain` occur only in that docstring, and the `Part 3` sections are empty `namespace` blocks. The file does contain `ClassicalBracketProg` (a temporary-AND bit-semantics AST) and the `zeroSetProj` machinery.

I therefore had no reference adder to adapt, and I did not import the module. I looked at it for API patterns only.

## 4. What is NOT done, with honest cost

The circuit half has roughly the pieces below. The size estimates are my own and are unproved.

| Piece | Done | Missing |
|---|---|---|
| Composition algebra (`CleanOps`) | Same-register sequencing, chains, sub-register lifting, catalytic sequencing. | A rule for `qIf` and `measure` (needed for measurement-based uncompute inside larger programs). Relocation between different `n` (`onRegister`, the reference's `pullbackAssertion`, about 1,000 lines). Parallel composition on disjoint registers. |
| `TOFF = 0` / `T` bounds | Additive algebra, `T = 4` per Jones Toffoli, `T = 0` for `CZ`. | A closed-form `T` bound in `N, M, aleph, beth` (that is, `thcTCost`). Counting for QROM, adder, comparator and Givens networks. |
| Clean Jones-AND / CZ / multi-CZ | Jones Toffoli on any target, `CZ`, Toffoli chains. | `czUnitary = diag(1,1,1,−1)`. Multi-controlled `Z` ladders. `CCZ`. |
| General-β catalytic rotation | Exact kickback, controlled-adder eigenvector, bridge lemma. | **The adder circuit itself** (ripple-carry or Gidney, with a `T`-count `O(β)` proof, about 800–1,500 lines). **The register-level net-action proof** (`hnet` of `catalytic_of_net_action`: the `V⁻¹ · Add · V` action on clean `rT, rS, rC` through `rS.concat rC` index splitting, about 300–600 lines). |
| Givens network (`GivensCircuit`) | Nothing. | Fermionic Gaussian-unitary conjugation of the JW annihilation operators for general `N`, the cascade, wires `2p + σ`, and the exact `givensLeaf` angle grid (reference `SpinSegregationGivens`, 748 lines, is the model). |
| Alias PREP (`AliasCircuit`) | Nothing circuit-level. (`Alias.lean` is the classical decomposition, `LCUa.lean` the abstract state-prep unitary.) | QROM of `keep`/`alt`, comparator, controlled swap, with `Alias.lean` mapped to amplitudes. |
| SELECT circuit | Nothing circuit-level. (`Select.lean` is the abstract involutive `S`.) | Sign handling, the four spin combinations, the π-swap, the `Z_{u_ℓ,σ}` terms. |
| 7 frozen holes | 0 / 7 | All of them. |

By the Round 2 estimate of 5–10k lines of remaining effort, Round 3 contributed about 650 lines, **under 10%**. The new lines are the foundation of the composition and cost algebras and the one analytically non-trivial identity (exact phase kickback). They are not any of the large circuit proofs.

## 5. Recommended next step

1. **`czUnitary = diag(1,1,1,−1)`.** A short entry-wise computation. Then `CCZ` as H · Toffoli · H on the lifted target, using `exists_jonesToffoli_on_target` with `realizesClean_seq` and `realizesClean_gate1`.
2. **A `qIf`/`measure` composition rule in `CleanOps`.** This is the missing structural piece for mixing Jones uncompute inside larger programs.
3. **The register-level `hnet`.** Prove `V⁻¹ · Add · V` acts on clean `rT, rS, rC` as `diag(exp(2π i t/2^β))` via `tensorState` and `embedMatrix_mulVec_tensorState`, instantiating `controlledAdd_kick`.
4. **Then the adder circuit.** A Toffoli-based ripple-carry adder over `exists_toffoli_chain` has `TOFF = 0` and `T = 4 · (number of Toffolis)`. Its clean-subroutine correctness needs a bit-level `evalBits` lemma for `X/CNOT/TOFF` circuits. Only then can `RealizesCatalyticSubroutine` with `T = O(β)` be stated.
5. **Only then** Givens and alias, and the 7 holes.

## 6. Numbers

No proved numbers exist. The Round 1 projections remain unproved orientation figures: Reiher `α ≈ 326.5`, Li `α ≈ 1550.8`, with Lee et al. needing 2.12e10 and 1.28e11 `T` gates. They are not `thcTCost` values.
