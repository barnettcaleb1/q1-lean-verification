# Verification record

Release 0.1.0 was checked locally on **12 September 2026**, using Lean 4.33.1 and the dependency revisions in [lake-manifest.json](lake-manifest.json).

| Check | Result |
| --- | --- |
| Standalone package build | Passed; all 34 Q1 proof modules and the public umbrella compiled |
| Axiom audit | Passed for 383 named declarations |
| Allowed axioms observed | `propext`, `Classical.choice`, `Quot.sound` only |
| Verification-tool regression tests | 5 tests passed, covering admissions, incomplete or malformed audit output, and changed source files |
| Proof-source preservation | All 34 Q1 modules match the previously frozen verification source bytes |

The standalone package began with an empty project build directory. It reused the already installed, pinned dependency source trees and mathlib compiled cache on macOS arm64; it did not rebuild all of mathlib from source or test a fresh network download. The project output was:

```text
Build completed successfully (3234 jobs).
PASS: build and 383 axiom checks; only Classical.choice, Quot.sound, propext.
```

The 383 checks cover 379 named constants in the theorem/definition inventory plus four concrete algebra instances. The final checks include `Q1.q1_srd` and `Q1.q1_rd`. [Audit.lean](Audit.lean) contains the explicit declaration list, and [verification/source-manifest.json](verification/source-manifest.json) binds that list and all project Lean files to SHA-256 hashes. The verifier checks the complete source-file set, runs the build, compiles the audit with warnings treated as errors, and rejects unexpected axioms or incomplete output.

The proof modules are unchanged; the public `Q1.lean` entry point, audit coverage, documentation and verification script are packaging additions. The manifest is a reproducibility record, not a signature or independent certification. When the source changes, its hashes and the corresponding verification record need deliberate review and updating.

Formal checking establishes the encoded implications using the pinned Lean kernel and imported library. Assessing whether the definitions and hypotheses express the intended mathematical question is a separate reading task; [docs/THEOREMS.md](docs/THEOREMS.md) makes that correspondence explicit. Build success does not establish novelty or a publication claim.

The GitHub workflow is configured to run the same checks. It has **not yet run on GitHub**, because this artifact was prepared locally. The Linux CI run and a first-time dependency download remain to be exercised when the repository is pushed.
