# Pure-AI Disclosure and Research Provenance (Hexagon / arXiv Supplementary Statement)

**Manuscript Title:** Formally Verified Asymptotic Optimality of Parallel Find-Any Search and Machine-Checked Benchmark Improvements in Lean 4  
**Author (Direction & Supervision):** Robert Kadlec, Masaryk University, Brno, Czech Republic (ORCID: `0009-0003-9245-8130`, `kadlecr@mail.muni.cz`)  
**Companion Zenodo Archive:** `https://doi.org/10.5281/zenodo.24545553` (all versions: `https://doi.org/10.5281/zenodo.24545552`)  
**Date:** November 26, 2026  
**License:** CC BY 4.0 (manuscript and documentation); Apache License 2.0 (Lean 4 formalizations and Python scripts, compatible with upstream `google-deepmind/formal-quantum-computation`).

---

## 1. Nature and Scope of Purely AI-Generated Execution

This work constitutes **purely AI-generated research** directed, scoped, and supervised by the human author (**Robert Kadlec**, Masaryk University, Brno, Czech Republic, who assumes full scholarly responsibility for the integrity, accuracy, and publication of all reported results), and forms part of a broader research project investigating the respective competencies of humans and large language models. No new mathematical derivation, circuit table, Lean 4 proof module, verification script, numerical enclosure, or paragraph of manuscript prose was manually written by the human author. All technical execution and adversarial refereeing were delegated to an explicit **multi-AI collaborative and adversarial workflow** running locally on a single Windows workstation (`32 GB` RAM), extending the multi-agent research-wiki methodology of Shirobokov et al. (`arXiv:2611.09822v3`).

### Roles of the AI Systems

| Agent / System | Primary Role | Concrete Contributions |
|---|---|---|
| **Antigravity / Gemini Coordinator** | Direction execution, environment isolation, exploratory algebraic analysis, same-kernel `leanchecker` replays, non-vacuity witness, manuscript assembly, and release packaging | Isolated Lean `4.35.0` toolchain setup; initial `Op102` simulator (`op102_sim.py`), symplectic `hGadget` block decomposition, ancilla liveness peak analysis (`50/50` across 8 stages), and HJB optimality analysis for `GroverFindAny`; dedicated same-kernel `leanchecker.exe` replays across `Track2Grover`, `Track2Weak` (`111/111`), `DisjointWitness` (`1/1`), and `Track1THC` (`9/9`); canonical 100-qubit `DisjointWitness.lean` proof; surgical git patch (`arcsin_366200.patch`), fresh Arb ULP sweep (`receipts/track3_arcsin/track3_ulp_sweep_final.json`), static LaTeX linting (enforcing strict passive voice), local Tectonic PDF compilation, and final Hexagon/GitHub/Zenodo packaging. |
| **OpenAI Codex (`gpt-6.2-astra`, ULTRA / high-effort CLI)** | Algorithm synthesis, Lean `4.35.0` proof engineering, numerical enclosure scripts, and technical drafting | Synthesized and formally verified the general adaptive `GroverFindAny` exact optimality theorem (`FindAnyLowerBound.lean`, `TighterFindAny.lean`), `ArcsinK25ConstCost = 366,200` (`s3aOps` GF(2) polar-matrix gadget reduction `-24 T`, `s4_2Ops` rank-one product basis square `-12 T`, `ExactPublic.exactPublicK25`), `GroverFindAll` sign-only (`27,014,193,664 / 10^12`) and coherent weak-measurement Kraus filter (`Track2Weak.FindAllWeak`, `26,768,771,052 / 10^12`), plus GF(2) degree-18, Pfaffian, and MILP follow-up analyses. |
| **Anthropic Claude Code (`sonnet`, `claude-fable-5-2` `xhigh` CLI) & OpenAI ChatGPT Web (`6 Pro`)** | Independent read-only adversarial refereeing (Tracks 2 & 3, `Track2Weak`, and the manuscript), exact numerical recomputation, and Appendix B (`Track1THC`) authorship | Performed ruthless read-only adversarial audits of Track 2 (`FindAll`, `FindAnyLowerBound`, `TighterFindAny`), Track 3 (`ArcsinK25ConstCost = 366,200`, `exactPublicK25`, `ulp_sweep`, degree/Pfaffian certificates), `Track2Weak` receipts, and the manuscript and release bundle (never auditing code authored by itself); independently authored 9 partial Lean `4.35.0` foundation modules (`1,956` lines) for the open `THCFactorization` benchmark (`0/7` definition holes + `0/2` public theorems filled); followed by deep manuscript-vs-Lean cross-audit under `claude-fable-5-2` (`xhigh`) and independent PDF mathematical refereeing via ChatGPT Web `6 Pro` (November 26, 2026). |

---

## 2. Deterministic Machine Verification Without Trusting Any LLM

For Tier (A) and Tier (B) claims, no unchecked LLM output is accepted as a formal proof: every formal statement rests on deterministic, machine-checkable Lean `4.35.0` proofs verified against **byte-for-byte frozen upstream specifications** from `google-deepmind/formal-quantum-computation`, whereas Tier (C) claims rest independently on explicitly identified numerical certificates and paper arguments:

1. **Frozen Read-Only Upstream Repositories:**
   - `formal-quantum-computation` (`main`, commit `489edc7039aa4cdded53724b39ea90e33d2c88b4`) — unmodified (`git status` empty; all 57 `QuantumComputation` source files and all 15 `QuantumComputationSpecs` files [7 `.lean`, 7 challenge JSONs, and `ChallengeJsons/README.md`] verified byte-identical to the build environment).
   - `discoveries_ref` (`discoveries`, commit `a88de8ff65d78af564b2373088ca369dc95f6547`) — unmodified baseline for diffs and `git apply --check`.
2. **Pinned Lean `4.35.0` Toolchain & Kernel Replay (`288/288` Modules):**
   - `Lean (version 4.35.0, x86_64-w64-windows-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)`
   - `lean.exe` SHA-256: `ec7a472d1c12a09b0c0c718f7427c2be527b3f5f07810fdbe076c2507c7a91ea`
   - `leanchecker.exe` SHA-256: `9ef6baeb28d5e28897d5ed6dddd60ff81e511d97374013ece435dff38e9e0137`
   - *Reconciliation of verified modules vs. staged files:* The five verified closures total `288` modules (`31` Track 2B/C + `20` Track 3 [`16` arcsine + `Track3Audit` + `ExactCount` + `ExactPublic` + `DisjointWitness`] + `117` Track 2A + `111` Track 2W + `9` Track 1). The release stages `279` `.lean` files because Track 3 omits `11` unmodified byte-identical upstream arcsine files and includes `2` standalone helper scripts (`CompareFrozen.lean`, `ReplacementTables.lean`): `20 - 11 + 2 = 11`, giving `31 + 11 + 117 + 111 + 9 = 279`.
   - *Transparency note on checker independence:* `lean` and `leanchecker` share the Lean `4.35.0` C++ kernel implementation; in addition, all five flagship theorems of `FindAnyLowerBound` and four public theorems of `TighterFindAny` were independently accepted by two non-Lean third-party kernels (`nanoda` 0.4.19: `49,235` and `46,246` declarations; `con-ron --verified`: `47,256` and `44,302` declarations; `receipts/external_checkers/`). Interface fidelity against frozen specs was verified via `CompareFrozen.lean` and `interface.py` (the upstream `lake comparator` requires Linux sandboxing and was not run on this Windows host with WSL disabled).
3. **Zero Proof Placeholders & Standard Axioms Only:**
   - Across all `279` staged `.lean` files: `0` occurrences of `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern`, `ofReduceBool`, or `trustCompiler`. (`decide +kernel`, which performs kernel reduction without `ofReduceBool`, is used in 144 files.)
   - Every public theorem depends strictly on subsets of `[propext, Classical.choice, Quot.sound]`; pure integer comparisons (`arcsinK25ConstCost < 369800`, `groverFindAllCells_nonempty`) depend on no axioms at all.
4. **Independent Adversarial Cross-Audit:**
   - Tracks 2 and 3, `Track2Weak`, and the manuscript and release bundle were audited in read-only mode by Claude Code (never auditing code authored by itself). **Track 1 (`Track1THC`, partial foundations) was authored by Claude Code and was NOT independently audited by another agent**; its 9 modules are verified by the `leanchecker.exe` replay in `receipts/track1_thc_partial/track1_thc_9modules_leanchecker.json`.
   - All substantive findings from internal audits and external review (including Fang–Heunen 2026 positioning, Belovs–Yolcu 2023 comparison, full 5-step loop-limit proof presentation, `DisjointWitness.lean` non-vacuity proof, explicit Appendix A schedule tables, `288`/`279` file-count reconciliation, and `Track1THC` relocation to Appendix B) were resolved before release packaging.

---

## 3. Explicit Epistemic Boundaries

To prevent any misreading of scope:
- **Machine-checked Lean `4.35.0` theorems** are separated from **external Arb/Python certified numerics** (notably the externally enclosed `GR0` reference constant `[0.06957627832198676185, 0.06957627832198676734]` used only to translate Lean's certified relative-cost upper bounds into `GR0 / relCost` factors), **restricted-model paper lower bounds and bounded search screens** (GF(2) degree-18 stage bounds, restricted Pfaffian reverse-square obstruction, MILP bounded infeasibility screens), and **partial foundations** (`Track1THC`: 9 verified modules, `0/7` frozen candidate definition holes + `0/2` public theorems filled).
- For `GroverFindAll`, all formal theorems apply to the single claimed cell `(1024, 512)`. All three walks (the pinned discovery, the sign-only walk, and `Track2Weak.FindAllWeak`) inherit the upstream engine cutoff `n >= 80,000` (search space `2^{80,000}`, `81,921,024` logical qubits for oracle slots alone, falling back to the exact `Stage1` circuit below `80,000`). For `Track2Weak.FindAllWeak`, the companion theorem `FiniteFromCutoff.groverFindAll_cost_from_80000` proves the claimed bound `r_weak = 26,768,771,052 / 10^12` uniformly for every `n >= 80,000`, placing these protocols in an asymptotically motivated regime with finite guarantees above an astronomically large cutoff.
- Human peer review has not yet been performed on this preprint. Full Lean sources, receipts, and SHA-256 manifests are archived in the accompanying GitHub/Zenodo release for independent reproduction.
