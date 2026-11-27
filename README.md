# Formally Verified Asymptotic Optimality of Parallel Find-Any Search and Machine-Checked Benchmark Improvements in Lean 4

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24545552.svg)](https://doi.org/10.5281/zenodo.24545552)
[![License: Apache-2.0](https://img.shields.io/badge/Code_License-Apache--2.0-blue.svg)](./LICENSE)
[![License: CC BY 4.0](https://img.shields.io/badge/Manuscript_License-CC_BY_4.0-lightgrey.svg)](./LICENSE-CC-BY-4.0.txt)
[![Lean 4.35.0](https://img.shields.io/badge/Lean-4.35.0-purple.svg)](https://leanprover.github.io/)
[![Baseline: arXiv:2611.09822v3](https://img.shields.io/badge/Baseline-arXiv%3A2611.09822v3-b31b1b.svg)](https://arxiv.org/abs/2611.09822)

**Author (Direction & Supervision):** Robert Kadlec, Masaryk University, Brno, Czech Republic ([ORCID 0009-0003-9245-8130](https://orcid.org/0009-0003-9245-8130), `kadlecr@mail.muni.cz`)  
**Research provenance:** Purely AI-generated research directed and supervised by the author (by whom full scholarly responsibility is assumed), forming part of a broader research project investigating the respective competencies of humans and large language models; all new mathematical derivations, circuit synthesis, Lean `4.35.0` formalizations, numerical enclosures, adversarial audits, and manuscript text were executed entirely by AI systems (Antigravity/Gemini Coordinator, OpenAI Codex `gpt-6.2-astra`, Anthropic Claude Code `sonnet` and `claude-fable-5-2` `xhigh`, and OpenAI ChatGPT Web `6 Pro`; see [`AI_DISCLOSURE_AND_PROVENANCE.md`](./AI_DISCLOSURE_AND_PROVENANCE.md)).

This repository archives the complete Lean `4.35.0` source files, verification receipts, Arb/Python audit-trail scripts and certificates, surgical DeepMind pull-request patch, and LaTeX/PDF manuscript (`paper/main.tex`, `paper/main.pdf`) addressing the frozen benchmarks in [`google-deepmind/formal-quantum-computation`](https://github.com/google-deepmind/formal-quantum-computation) ([Shirobokov et al., `arXiv:2611.09822v3`](https://arxiv.org/abs/2611.09822)).

---

## Stratified Results (Pinned Upstream: `main` `489edc70`, `discoveries` `a88de8ff`)

| Benchmark / Track | Prior Baseline (`arXiv:2609.39621`, `arXiv:2611.09822v3`) | Present Work | Contribution | Epistemic Tier | `leanchecker` (`v4.35.0`) |
|---|---|---|---|---|---|
| **`GroverFindAny`** *(flagship; all `121` grid cells)* | Constant `1/2 + 1/π` & single-checkpoint infimum (Fang & Heunen, 2026); parallel upper bound (Shirobokov et al., 2026) | **`IsGLB {R \| Feasible m k R} (1/2 + 1/π)`** + finite-`n` `actual_expected_rounds` | **General adaptive optimality** across all `OracleDynamicCircuit` programs (arbitrary workspace, adaptive measurements, nested `qWhile` loops) | **(A) Lean 4.35.0** | `31/31` exit `0` *(shared with `TighterFindAny`)* |
| **`ArcsinK25ConstCost`** *(Construction I; `Q2.23`, `100 Q`)* | `369,800` (`3,698 T × 100 Q`, `TOFF = 0`) | **`366,200`** (`3,662 T × 100 Q`, `TOFF = 0`) + exact compiled count `exactPublicK25` & `DisjointWitness` | **`-3,600` spacetime (`-36 T`, `-0.9735%`)**; surgical `5/16`-module diff + 100-qubit non-vacuity witness | **(A) Lean 4.35.0** | `20/20` exit `0` |
| **`GroverFindAll` `(1024, 512)` sign-only** *(Construction II)* | `27,024,465,988 / 10^12` (`≥ 2.574566×` asymptotic vs ext. GR0) | `27,014,193,664 / 10^12` (`≥ 2.57554525548×` asymptotic vs ext. GR0) | `-0.038011%` certified upper bound (`117` modules; eventual, `n ≥ 80,000` engine) | **(A) Lean / (C) GR0** | `117/117` exit `0` |
| **`GroverFindAll` `(1024, 512)` weak filters** *(Construction II)* | Pinned discovery (`≥ 2.574566×` asymptotic vs ext. GR0) | **`26,768,771,052 / 10^12`** (**`≥ 2.599158481606×`** asymptotic vs ext. GR0) | **`-0.946%` vs pinned (`-0.908%` vs sign-only)**; 14 Kraus filters (all `n ≥ 80,000` via `QuantumComputation.Specs.groverFindAll_cost_from_80000`) | **(A) Lean / (C) GR0** | `111/111` (`v1.0.0`) + post-fix `FindAllWeak`/`FiniteFromCutoff` exit `0` |
| **`THCFactorization`** *(Appendix B; open benchmark)* | No discovery impl. on `discoveries`; unsolved in this release | `9` verified foundation modules (`1,956` lines; authored by Claude Code, not independently audited) | LCU/JW/alias/select + clean/catalytic algebra (**`0/7` def. holes + `0/2` thms filled**) | **(B) Partial** | `9/9` exit `0` |

*Note on `TighterFindAny`:* Recorded as a minor technical remark (precision refinement of `-1.5915×10^-21` at Mathlib's `Real.pi_gt_d20` ceiling on the unchanged circuit of Shirobokov et al., 2026), not an algorithmic contribution.

### Soundness, Module Reconciliation & Epistemic Hygiene
- **Verified modules vs. staged files (`288` vs. `279`) and `v1.0.0` vs. `v1.0.1` receipts:** In initial release `v1.0.0`, all `288` Lean `4.35.0` project modules (`31 + 20 + 117 + 111 + 9 = 288`) passed `leanchecker` exit `0` on Windows (including the historical `111/111` `Track2Weak` replay `receipts/track2_weak/track2weak_clean_all_leanchecker.json` and `final_semantic_axioms.json`, where `Track2Weak/FindAllWeak.lean` had SHA-256 `d210ff50...ac929`). In `v1.0.1`, only `Track2Weak/FindAllWeak.lean` changed (by one keyword: `def` → `abbrev`, SHA-256 `8ba16994...470bdd9a`; the other `110` `Track2Weak` sources are unchanged byte-for-byte), and the two recompiled modules (`Track2Weak.FindAllWeak` and `Track2Weak.FiniteFromCutoff`) are freshly verified in `receipts/track2_weak/v1_0_1_postfix/postfix_track2weak_leanchecker.json` (`4/4` exit `0`) and `receipts/linux_comparator/run2_findall/fix16/`. The release stages `279` `.lean` files because Track 3 (`20` verified modules: `16` arcsine + `Track3Audit` + `ExactCount` + `ExactPublic` + `DisjointWitness`) omits `11` unmodified byte-identical upstream arcsine files and includes `2` standalone helper scripts (`CompareFrozen.lean`, `ReplacementTables.lean`): `20 - 11 + 2 = 11`, yielding `31 + 11 + 117 + 111 + 9 = 279`.
- **Zero proof placeholders:** Comment-stripped static scans across all `279` staged `.lean` files report `0` hits for `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`, `implemented_by`, `extern`, `ofReduceBool`, and `trustCompiler`. (`decide +kernel`, performing kernel reduction without `ofReduceBool`, is used in `144` files.)
- **Standard axioms only:** Every public theorem depends strictly on subsets of `[propext, Classical.choice, Quot.sound]` (`arcsinK25ConstCost < 369800` and `groverFindAllCells_nonempty` depend on no axioms at all). Every archived receipt contains `0` occurrences of `sorryAx`.
- **Kernel & official Linux `lake comparator` verification:** `lean` and `leanchecker` invoke the Lean `4.35.0` kernel implementation (pinned toolchain `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`). Independently on a separate 64-bit Linux host (`Ubuntu 26.04.1 LTS`, `62 GiB` RAM, `bubblewrap 0.11.1` sandbox, without `--inadvisably-no-sandbox`), all four challenge constructions passed the official upstream `lake comparator` driver (curated receipt subset with verbatim `RESULT_SHA256SUMS.txt` manifests and challenge configs in `receipts/linux_comparator/`): `ArcsinK25ConstCost = 366,200` (verbatim `discoveries` `ArcsinK25ConstCost.json`, `1,426 s`, plus upstream `lake test` PASS), `Track2Grover.TighterFindAny` (`330 s`), sign-only `Track2Grover.FindAll` (`3,402 s`, `13.14 GiB` = `14.11 GB` whole-job cgroup peak), and weak-filter `Track2Weak.FindAllWeak` (`2,007 s`, `6.57 GiB` = `7.06 GB` whole-job cgroup peak, after the `v1.0.1` one-keyword fix `noncomputable def weakChosenBatch` → `noncomputable abbrev weakChosenBatch` on line 30 restoring `groverFindAllProgram` `ReducibilityHints.regular(37)` matching the challenge module via the same `abbrev` device used in upstream `StageLoop.lean` line 2327; SHA-256 `8ba16994...bdd9a`). All five flagship theorems of `FindAnyLowerBound` and four challenge theorems of `TighterFindAny` were also independently accepted by two third-party Rust Lean 4 checkers bundled with Lean `4.35.0`: `nanoda_bin` 0.4.19 (`https://github.com/ammkrn/nanoda_lib`; `49,235` and `46,246` expanded constants, standard axioms only) and `con-ron --verified` (`47,256` and `44,302` `lean4export` 3.1.0 declaration records; wrapper and receipts in `receipts/external_checkers/`).
- **Asymptotic & external-GR0 boundaries:** For `GroverFindAll`, all formal theorems apply to the single claimed cell `(1024, 512)`. All three walks (the pinned discovery, the sign-only walk, and `Track2Weak.FindAllWeak`) inherit the upstream engine cutoff `n >= 80,000` (search space `2^{80,000}`, `81,921,024` oracle-slot qubits before additional workspace, falling back to exact `Stage1` below `80,000`). For `Track2Weak`, `QuantumComputation.Specs.groverFindAll_cost_from_80000` (declared in `Track2Weak/FiniteFromCutoff.lean`) proves the claimed bound `r_weak = 26,768,771,052 / 10^12` uniformly for every `n >= 80,000`, making these asymptotically motivated constructions with finite guarantees above an astronomically large cutoff. Asymptotic speedup multipliers (`≥ 2.57554525548×` and `≥ 2.599158481606×`) divide an externally enclosed 256-bit Arb lower bound for `GR0` (`[0.06957627832198676185, 0.06957627832198676734]`) by the Lean-certified upper bound.
- **Excluded development clutter:** See [`EXCLUDED.md`](./EXCLUDED.md) for the exact inventory of 3 unreachable exploratory files, 29 superseded historical logs, and 1 superseded pre-final ULP receipt omitted from this release.

---

## Repository Layout

- `paper/main.tex` & `paper/main.pdf` — Complete, engine-neutral pure-ASCII LaTeX manuscript and Tectonic-compiled PDF (static-lint verified: 0 lint errors, 0 first-person pronouns, 0 Overfull `\hbox`, 0 badness-10000 Underfull `\hbox`, and 0 `LaTeX Warning:` diagnostics; ready for Hexagon, Overleaf, and arXiv).
- `patches/arcsin_366200.patch` — Surgical 5-file git patch against `google-deepmind/formal-quantum-computation` branch `discoveries` (`a88de8ff65d78af564b2373088ca369dc95f6547`), verified with `git apply --check`.
- `lean/track3_arcsin/` — The 5 modified `Arcsin` modules + `Track3Audit.lean`, `ExactCount.lean`, `ExactPublic.lean`, `DisjointWitness.lean`, `CompareFrozen.lean`, `ReplacementTables.lean`, `replacements.json`, archived audit-trail scripts (`scripts/README.md`), and boundary notes.
- `lean/track2_grover/` — All `31` modules of `FindAnyLowerBound` + `TighterFindAny`, all `117` modules of `FindAll` (sign-only), and exact schedules/Arb numerics (`kicks24.json`, `gr0_1024_512.json`, `refine_placement0.json`, `enclose.py`).
- `lean/track2_weak/` — All `111` `Track2Weak` Lean `4.35.0` modules implementing the 14-filter coherent weak-measurement Kraus protocol (`Track2Weak.FindAllWeak`) + verification scripts.
- `lean/track1_thc_partial/` — `9` verified partial foundation modules (`Track1THC`, `0/7` frozen definition holes + `0/2` public theorems filled; see its local `README.md`).
- `receipts/` — Clean, verified final compiler logs, `leanchecker` replay logs (including `track3_disjoint_witness_leanchecker.json`, `track2weak_clean_all_leanchecker.json`, `findall_replay_manifest.json`, and `track1_thc_9modules_leanchecker.json`), independent 64-bit Linux official `lake comparator` (`bwrap` sandbox) and `lake test` receipts (`linux_comparator/run1_fast/` and `linux_comparator/run2_findall/` including `fix16`), independent third-party kernel receipts (`external_checkers/external_findany_lowerbound.json` and `external_findany_tighter.json` from `nanoda 0.4.19` and `con-ron --verified`), frozen-interface JSON comparisons, final Arb ULP sweep (`track3_ulp_sweep_final.json`), and MILP/degree/Pfaffian receipts.
- `SHA256SUMS.txt` — Complete SHA-256 manifest of every file in this release.
- `AI_DISCLOSURE_AND_PROVENANCE.md` — Full Hexagon/arXiv pure-AI provenance statement.
- `NOTICE` — Apache-2.0 attribution for the 32 upstream-derived Google LLC files with verbatim headers plus 1 docstring-attributed partial module (33 files referencing Google LLC).
- `EXCLUDED.md` — Transparent list of excluded non-production development files.

---

## Quick Reproduction (`ArcsinK25ConstCost = 366,200`)

```bash
export BUNDLE=/absolute/path/to/this-repo
git clone --branch discoveries https://github.com/google-deepmind/formal-quantum-computation.git arcsin-review
cd arcsin-review
git checkout --detach a88de8ff65d78af564b2373088ca369dc95f6547
git apply --check "$BUNDLE/patches/arcsin_366200.patch"
git apply "$BUNDLE/patches/arcsin_366200.patch"

export LEAN_NUM_THREADS=1
lake exe cache get
lake build +QuantumComputationSpecs.Primitives.Arcsin +QuantumComputationDiscoveries.Primitives.Arcsin
lake env leanchecker --verbose QuantumComputationDiscoveries.Primitives.Arcsin
lake env lean --run "$BUNDLE/lean/track3_arcsin/CompareFrozen.lean"
# Optional: also run the upstream comparator and standalone exact-count / non-vacuity proofs:
lake comparator --config QuantumComputationSpecs/ChallengeJsons/Primitives/ArcsinK25ConstCost.json
lake env bash -eu -c '
  src="$BUNDLE/lean/track3_arcsin/m1"
  obj=$(mktemp -d)
  export LEAN_PATH="$obj${LEAN_PATH:+:$LEAN_PATH}"
  for m in ExactCount ExactPublic DisjointWitness; do
    lean -j 1 --root="$src" -o "$obj/$m.olean" "$src/$m.lean"
    leanchecker --verbose "$m"
  done
'
```

---

## Quick Reproduction (`GroverFindAny` Optimality & `GroverFindAll` Comparator on Linux)

From a clean checkout of `google-deepmind/formal-quantum-computation` (`discoveries`, `a88de8ff`) after `lake exe cache get`:

```bash
cp -a "$BUNDLE/lean/track2_grover/Track2Grover" .
cp -a "$BUNDLE/lean/track2_weak/Track2Weak" .
cat >> lakefile.toml <<'EOF'

[[lean_lib]]
name = "Track2Grover"
globs = ["Track2Grover.+"]

[[lean_lib]]
name = "Track2Weak"
globs = ["Track2Weak.+"]
EOF
export LEAN_NUM_THREADS=1
lake build +QuantumComputationSpecs.Algorithms.Grover +Track2Grover.FindAnyLowerBound +Track2Grover.TighterFindAny
lake env leanchecker --verbose Track2Grover.FindAnyLowerBound
lake comparator --config "$BUNDLE/receipts/linux_comparator/comparator_configs/GroverFindAny_TighterFindAny.json"
# Optional FindAll comparators (~6.6 GiB / ~13.1 GiB cgroup peak):
lake build +Track2Weak.FindAllWeak +Track2Weak.FiniteFromCutoff +Track2Grover.FindAll
lake comparator --config "$BUNDLE/receipts/linux_comparator/comparator_configs/GroverFindAll_FindAllWeak.json"
lake comparator --config "$BUNDLE/receipts/linux_comparator/comparator_configs/GroverFindAll_SignOnly.json"

# Portable third-party Rust checker replay (nanoda_bin 0.4.19 & con-ron --verified, bundled with Lean 4.35.0):
lake env leanexport Track2Grover.FindAnyLowerBound -- \
  Track2Grover.FindAnyLowerBound.finite \
  Track2Grover.FindAnyLowerBound.actual_expected_rounds \
  Track2Grover.FindAnyLowerBound.asymptotic_real \
  Track2Grover.FindAnyLowerBound.no_smaller_rational \
  Track2Grover.FindAnyLowerBound.exact_infimum > findany_lb.ndjson
cat > nanoda.json <<'JSON'
{"export_file_path":"findany_lb.ndjson","use_stdin":false,"permitted_axioms":["propext","Classical.choice","Quot.sound"],"unpermitted_axiom_hard_error":true,"nat_extension":true,"string_extension":true,"print_success_message":true}
JSON
lake env nanoda_bin nanoda.json
lake env con-ron --verified findany_lb.ndjson
```

*Receipt inventory note:* `receipts/linux_comparator/` preserves the verbatim `RESULT_SHA256SUMS.txt` manifests from the Linux verifier alongside a curated publication subset (`35/71` listed files plus reports, diagnostics, and configs); similarly, the historical `v1.0.0` `receipts/track2_weak/final_semantic_axioms.json` references three raw Windows workstation audit files (`semantic_axioms.stdin.txt` and timestamped raw logs) omitted from staging to avoid path-specific clutter.

## Citation & Attribution

Cite [`CITATION.cff`](./CITATION.cff) together with the foundational prior works:
- S. Shirobokov et al., *"Discovering formally verified quantum programs with AI"*, [`arXiv:2611.09822v3`](https://arxiv.org/abs/2611.09822) (2026).
- W. Fang and C. Heunen, *"Weakly measured loops for quantum amplitude amplification: oracle savings and adaptive search with unknown target probability"*, [`arXiv:2609.39621`](https://arxiv.org/abs/2609.39621) (2026).

See [`NOTICE`](./NOTICE) for full Apache-2.0 copyright attribution of upstream-derived files (`Copyright 2026 Google LLC`).

## License

- All Lean 4 formalization files (`lean/`, `patches/`) and Python scripts are licensed under the **Apache License, Version 2.0** (`LICENSE`), matching upstream `google-deepmind/formal-quantum-computation`.
- The manuscript (`paper/main.tex`, `paper/main.pdf`) and documentation are licensed under **Creative Commons Attribution 4.0 International (CC BY 4.0)** (`LICENSE-CC-BY-4.0.txt`).
