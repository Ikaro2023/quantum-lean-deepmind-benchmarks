# TRACK 1 ROUND 2 (THCFactorization) — Final Report (Team 1 / Claude Code)

Date: 2026-11-25. Toolchain: Lean 4.35.0 (isolated `.elan`), Mathlib/physlib as in `work_repo`.
This report covers the interrupted-and-resumed run (host restart at 17:46:34).

## 0. Bottom line (read first)

**`THCFactorization.json` is NOT solved. 0 of the 7 frozen holes are filled, and `thc_correctness` and `thc_t_cost` are not proved.**
There is no proved `thcTCost` or `thcTotalLogicalQubits`, so there are **no proved numbers for Reiher (N=54, M=350) or Li (N=76, M=450)**.
Nothing below should be described as "the solution".

Round 2 added the **abstract LCU / block-encoding half**. This is a pure-math existence result: the unitary `U` exists and satisfies the frozen
`IsQubitizedBlockEncodingUnitary`. It contains **no circuit**. The circuit half (what `thc_correctness` needs through
`RealizesCatalyticSubroutine`, and all of `thc_t_cost`) has not been started in earnest.

## 1. Status of the 7 holes

| # | Hole | Status |
|---|---|---|
| 1 | `thcBlockAncillas` | not filled |
| 2 | `thcScratchAncillas` | not filled |
| 3 | `thcCatalystQubits` | not filled |
| 4 | `thcTCost` | not filled |
| 5 | `thcProgram` (spec name `thcCandidateProgram`) | not filled |
| 6 | `thc_correctness` | not proved (math half only, see §2) |
| 7 | `thc_t_cost` | not proved |

`Track1THC\Solution.lean` was **not created**, because there is nothing honest to put in it. The hole list also omits `thcCandidateAlpha` and
`thcCandidateOffset`, which are `sorry` in the spec too. A full solve has to choose them (e.g. `α` from `lamRep`, offset `c = ∑t − ½∑ζ` from `Centering`).

## 2. What is verified (6 modules, 1306 lines, 0 `sorry`, standard axioms only)

| File | Lines | Content |
|---|---|---|
| `Alias.lean` | 147 | `alias_exists`: exact Walker–Vose integer alias decomposition (Round 1) |
| `JWAlgebra.lean` | 567 | `jwAnnihilate_anticomm_conj`, `orbitalNumberOp_idem`, `orbitalReflection_conjTranspose`, `orbitalReflection_mul_self` (Round 1) |
| `Centering.lean` | 203 | `thc_centering`: exact `H − c•1 = ∑(−t/2)Z_u + (1/8)∑ζ Z Z`, 1-norm exactly `lamRep` (Round 1) |
| `LCUa.lean` | 33 | `exists_unitary_first_col`: unitary with prescribed real unit first column (**new, Round 2**) |
| `LCU.lean` | 255 | `lcu_blockEncoding`: `S` Hermitian involution, `W₀` with first column `a` ⇒ `∃ U, IsQubitizedBlockEncodingUnitary α A U` for arbitrary `k`, `m` (**new**) |
| `Select.lean` | 101 | `swapSelect`, `lcu_of_involutive_family`: for unitaries `V x` with an involution `π` such that `V (π x) = (V x)ᴴ`, and a `π`-symmetric probability vector `p`, `∃ U, IsQubitizedBlockEncodingUnitary α (α ∑ pₓ Vₓ) U` (**new**) |

`Select.lean` is the piece that was interrupted. The only fix it needed was deleting a redundant trailing `ring` (line 97, "no goals"); the rest compiled unchanged.
The swap in `swapSelect` (`S = ∑ V x ⊗ |π x⟩⟨x|`) is what makes `S` Hermitian even when `V x` is not, as with products `Z_a Z_b` of non-commuting reflections.
This addresses the "Hermitian SELECT" design risk from Round 1.

Mirrored (copy only) to `work_repo\Track1THC\`. `work_repo\lakefile.toml`, `formal-quantum-computation\`, `discoveries_ref\` and `THCFactorization.lean` were not touched.

### Verification evidence (this session)

* `lean.exe` (via `lc.sh Select -o`, `build` for earlier modules): all 6 modules exit 0 (only linter notes remain).
* `leanchecker.exe Track1THC.<M>` for M in Alias, JWAlgebra, Centering, LCUa, LCU, Select: **all exit 0**.
* `grep -c sorry Track1THC/*.lean`: 0 for every file. No custom axioms.
* `#print axioms` (file `track1_thc\scratch\Axioms.lean`, exit 0). Every theorem below depends on exactly `[propext, Classical.choice, Quot.sound]`:
  `Track1THC.alias_exists`, `LCU.exists_unitary_first_col`, `LCU.lcu_blockEncoding`, `LCU.swapSelect_conjTranspose`,
  `LCU.swapSelect_mul_self`, `LCU.lcu_of_involutive_family`, `JW.jwAnnihilate_anticomm_conj`, `JW.orbitalNumberOp_idem`,
  `JW.orbitalReflection_conjTranspose`, `JW.orbitalReflection_mul_self`, `Centering.thc_centering`.
* Not re-verified by me: the DeepMind reference oleans in `_build` (`Defs`, `ModularDefs`, `CleanDyn`, `SpinSegregationGivens`). They were compiled unmodified
  for inspection only. Nothing in `Track1THC` imports them, and I make no claim about them beyond "they compiled".

## 3. Why the remaining holes are not closed

`DynamicCircuit` consists of `Circuit` (primitive gates X, Y, Z, H, S, T, CNOT, SWAP, TOFF), `measure`, `qIf` and `seq`. There is **no arbitrary-unitary gate**,
so `thcCandidateProgram` cannot just be "the unitary `U` from `lcu_of_involutive_family`". `thc_correctness` demands an explicit
Clifford+T+measurement circuit whose `compile` realizes `U` as a clean, catalytic subroutine, including exact `givensLeaf` rotations at angles `2πk/2^β`.
Those angles are not exactly Clifford+T, which is why the phase-gradient catalyst and a catalytic adder are needed.

Missing pieces (honest list, none of which exist in `Track1THC`):

1. **`W` as a circuit and coherent alias PREP** (QROM of `keep`/`alt`, comparator, controlled swap), with `alias_exists` mapped to amplitudes. (`AliasBase/AliasPrep` in P450 are the model.)
2. **SELECT as a circuit**: sign handling, 4 spin combinations of `Z_{μσ}Z_{ντ}`, the π-swap, and the `Z_{u_ℓ,σ}` terms. Needs Givens-network conjugation of `Z_0` into `Z_{givensLeaf}` in JW form on wires `2p+σ`.
   (`SpinSegregationGivens.givensCascadeUnitary_conj_*` are the model.) Also needs exact catalytic rotations from `PhaseGradAdder`.
3. **Clean-subroutine composition theory** (`CleanDyn`, `CleanSimulates`, `CatalystCleanBridge`) adapted to general `N`, `M`, `β`, plus register-disjointness for arbitrary `n`.
4. **Resource counting**: `count TOFF = 0` (Jones AND/uncompute) and a closed-form `T` bound in terms of `N, M, ℵ, β` to define `thcTCost`.
5. Choosing the `α`, `c`, `Heff`, `εSynth` conventions, including the `lamRep = 0` edge. This part is easy, since `Centering` gives the exact identity, and `Heff` can be `thcHamiltonian` itself, which agrees with itself exactly.

I judged item 3 and the QHL bridge to be multi-thousand-line work. Starting it with the little time left after the restart risked leaving half-built, uncompilable modules, so I stopped at a clean state.

## 4. Numbers

No proved numbers exist. The Round 1 projections remain **unproved estimates**, for orientation only:
Reiher `d = 61,479`, `L = 16`, padded `α ≈ 326.5` (×1.066); Li `d = 101,551`, `L = 17`, padded `α ≈ 1550.8` (×1.291). Lee et al. need 2.12e10 and 1.28e11 `T` gates.
These are not `thcTCost` values and say nothing about whether a Lean-proved bound will be close.

## 5. Recommended next step

Pick one verified path and build it bottom-up. Concretely:

1. First prove the *non-catalytic* clean realization of a single `Z_{u,σ}`-select for fixed small `N` using the existing `jonesToffoli` realization, to learn the `RealizesCleanSubroutine` composition API.
2. Then adapt `CleanDyn`'s composition lemmas and `PhaseGradAdder` for general `β`.
3. Prove the Givens-conjugation lemma generally (adapt `SpinSegregationGivens`; compile with `buildref.ps1`).
4. Only then define the 7 holes and `Solution.lean`.

Estimated remaining effort is still on the order of 5–10k lines.
