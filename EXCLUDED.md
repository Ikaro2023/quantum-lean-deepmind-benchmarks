# Excluded Development Artifacts (Audit Trail Transparency)

To keep this public release minimal, self-contained, and free of dead code or superseded failed runs, the following non-production development files from the working campaign directory were intentionally excluded:

1. **Three unreachable exploratory Lean modules** (outside every public import closure of `FindAnyLowerBound`, `TighterFindAny`, `FindAll`, and `FindAllWeak`):
   - `Track2Grover/LowerOrdinal.lean`
   - `Track2Grover/LowerTagged.lean`
   - `Track2Grover/LowerVisits.lean`
2. **Twenty-nine superseded historical compiler/checker logs** from intermediate failed proof-development attempts under the working `track2_grover/receipts/` and `track2_grover/lower_bound/attempts.log` directories that recorded intermediate `sorryAx` states before final proof completion (e.g., early attempts of `CoupledActions`, `FirstQuery`, `SharpUpper`, `QueryAngle`). All included receipts correspond strictly to the final verified artifacts (`0` occurrences of `sorryAx`).
3. **One superseded pre-final Arb ULP sweep (`m3/ulp_sweep.json`)** whose `source_sha256.StageProofB.lean` (`b02618c4...`) predated the final two-line constant update (`6c570eca...`). It is replaced in this release by `receipts/track3_arcsin/track3_ulp_sweep_final.json`, which binds the exact final `StageProofB.lean` (`6c570eca74ba...`) and reproduces identical extremizers, error enclosures, and integer output digests.
4. **Compiled binary artifacts (`.olean`, `.ir`, `.lake` caches)** and the read-only clones of upstream `google-deepmind/formal-quantum-computation` (reproducible directly from GitHub commits `489edc70` and `a88de8ff`).
