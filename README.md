# Q1 Lean verification

Lean 4 verification of two implications concerning rapid decay and simplicity of the reduced group C*-algebra, motivated by Question 1 of Alam, Gondek, Kalantar and Pham, *Growth conditions for topological freeness*, [arXiv:2602.15009v2](https://arxiv.org/abs/2602.15009v2), Section 3.

The project uses a **finite symmetric generating set and its exact shortest word length**. It keeps the statements separate:

| Declaration | Hypotheses | Conclusion |
| --- | --- | --- |
| `Q1.q1_srd` | Ordinary subexponential reduced-norm growth and trivial amenable radical | Simplicity of the reduced group C*-algebra |
| `Q1.q1_rd` | Polynomial reduced-norm growth (RD) and trivial amenable radical | The same simplicity conclusion |

The [theorem guide](docs/THEOREMS.md) gives the precise quantifiers, norm, amenability and simplicity definitions. The Lean statements are in [FullSimplicity.lean](Q1/FullSimplicity.lean). This repository provides a verification artifact; it makes no claim of novelty or publication status.

## Build and verify

Install Git, Python 3.9 or newer, and Lean's [elan toolchain manager](https://github.com/leanprover/elan#installation). From this directory:

```sh
lake exe cache get
python3 scripts/verify.py
```

The first command fetches dependencies and their compiled mathlib cache. The verifier checks the source manifest, runs `lake build`, and audits 383 named declarations, including the final theorems and the concrete algebra instances. It rejects missing results and any axiom outside `propext`, `Classical.choice` and `Quot.sound`.

For a build alone, run `lake build`. The default [Q1.lean](Q1.lean) imports the full verification. For the raw axiom output, run `lake env lean -DwarningAsError=true Audit.lean`.

Lean is pinned to **4.33.1** and mathlib to commit **`0df444a360eaa60ab8c11dca51a86af692955474`**. The checked-in [Lake manifest](lake-manifest.json) fixes all transitive revisions. Keep it when cloning or publishing this repository. Dependencies and compiled outputs are downloaded locally and are not included in the source distribution.

[GitHub Actions](.github/workflows/verify.yml) runs the same verification on pushes and pull requests. See [VERIFICATION.md](VERIFICATION.md) for the recorded local checks and their limits, and [CONTRIBUTING.md](CONTRIBUTING.md) for changing the frozen source manifest.

## Attribution and license

Copyright 2026 Caleb Barnett. Project verification files are licensed under [Apache-2.0](LICENSE). Mathematical sources are credited in [REFERENCES.md](REFERENCES.md); dependency licenses and selected upstream formalization credits appear in [THIRD_PARTY.md](THIRD_PARTY.md) and [NOTICE](NOTICE). These credits distinguish the original mathematical sources from this verification artifact.
