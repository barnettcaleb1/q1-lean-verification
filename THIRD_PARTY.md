# Third-party software and formalization credits

The source distribution contains the project's verification sources and support files. Lean and Lake dependencies are fetched separately; their source trees, license files and compiled caches are not vendored here. The project license does not replace upstream licenses or claim ownership of their code.

## Pinned environment

[Lean 4](https://github.com/leanprover/lean4) version **4.33.1**, release commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, is licensed under Apache-2.0. The toolchain distribution retains its own third-party notices. [lean-toolchain](lean-toolchain) selects the release; [lake-manifest.json](lake-manifest.json) fixes the following dependency commits.

| Dependency | Exact revision | License at that revision |
| --- | --- | --- |
| [mathlib](https://github.com/leanprover-community/mathlib4) | [`0df444a360eaa60ab8c11dca51a86af692955474`](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474) | [Apache-2.0](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/LICENSE) |
| [plausible](https://github.com/leanprover-community/plausible) | [`b7eb3304aeae834b12dda98993a37f6a41f6f0bb`](https://github.com/leanprover-community/plausible/tree/b7eb3304aeae834b12dda98993a37f6a41f6f0bb) | [Apache-2.0](https://github.com/leanprover-community/plausible/blob/b7eb3304aeae834b12dda98993a37f6a41f6f0bb/LICENSE) |
| [LeanSearchClient](https://github.com/leanprover-community/LeanSearchClient) | [`5f4d51b81cbd3f6b32b156bfad9056621a040404`](https://github.com/leanprover-community/LeanSearchClient/tree/5f4d51b81cbd3f6b32b156bfad9056621a040404) | [Apache-2.0](https://github.com/leanprover-community/LeanSearchClient/blob/5f4d51b81cbd3f6b32b156bfad9056621a040404/LICENSE) |
| [importGraph](https://github.com/leanprover-community/import-graph) | [`16f02aa7642864af59f1ff0e384a015994db9118`](https://github.com/leanprover-community/import-graph/tree/16f02aa7642864af59f1ff0e384a015994db9118) | [Apache-2.0](https://github.com/leanprover-community/import-graph/blob/16f02aa7642864af59f1ff0e384a015994db9118/LICENSE) |
| [proofwidgets](https://github.com/leanprover-community/ProofWidgets4) | [`4be2e3d5087eeb272cf5a8853b8f9dd025ef5957`](https://github.com/leanprover-community/ProofWidgets4/tree/4be2e3d5087eeb272cf5a8853b8f9dd025ef5957) | [Apache-2.0](https://github.com/leanprover-community/ProofWidgets4/blob/4be2e3d5087eeb272cf5a8853b8f9dd025ef5957/LICENSE) |
| [aesop](https://github.com/leanprover-community/aesop) | [`3448c0bcc5ce01b2d1546e483ec3620e32df3d0e`](https://github.com/leanprover-community/aesop/tree/3448c0bcc5ce01b2d1546e483ec3620e32df3d0e) | [Apache-2.0](https://github.com/leanprover-community/aesop/blob/3448c0bcc5ce01b2d1546e483ec3620e32df3d0e/LICENSE) |
| [Qq](https://github.com/leanprover-community/quote4) | [`92c15be17b7caf78c2ad767ec40f89052d908d81`](https://github.com/leanprover-community/quote4/tree/92c15be17b7caf78c2ad767ec40f89052d908d81) | [Apache-2.0](https://github.com/leanprover-community/quote4/blob/92c15be17b7caf78c2ad767ec40f89052d908d81/LICENSE) |
| [batteries](https://github.com/leanprover-community/batteries) | [`4488d40d070b9700d4d5a6aa342f0d40c31b2a2d`](https://github.com/leanprover-community/batteries/tree/4488d40d070b9700d4d5a6aa342f0d40c31b2a2d) | [Apache-2.0](https://github.com/leanprover-community/batteries/blob/4488d40d070b9700d4d5a6aa342f0d40c31b2a2d/LICENSE) |
| [Cli](https://github.com/leanprover/lean4-cli) | [`6130a47896ce867c6a4a55373441e59e565bad0f`](https://github.com/leanprover/lean4-cli/tree/6130a47896ce867c6a4a55373441e59e565bad0f) | [MIT](https://github.com/leanprover/lean4-cli/blob/6130a47896ce867c6a4a55373441e59e565bad0f/LICENSE) |

Cli's upstream MIT license names **Copyright (c) 2021 mhuisi**. The other dependencies above retain their individual Apache-2.0 copyright notices and author credits. See the linked upstream license files; no upstream source is relicensed as Caleb Barnett's work.

## Selected upstream formalization credits

The entire mathlib community is credited for the imported library. The following source headers identify particularly relevant foundations used by this verification; this is not an exhaustive list of mathlib contributors.

- **Alena Gusakov, Bhavik Mehta and Kyle Miller**, `Mathlib/Combinatorics/Hall/Basic.lean`, copyright 2021. This supplies `Finset.all_card_le_biUnion_card_iff_exists_injective`, used in the invariant-mean-to-Følner proof.
- **Yaël Dillies and Stefano Rocca**, `Mathlib/MeasureTheory/Group/FoelnerFilter.lean`, copyright 2025 Stefano Rocca. This supplies the Følner-to-amenability theorem used by `FoelnerMean.lean`.
- **Heather Macbeth**, `Mathlib/Analysis/InnerProductSpace/l2Space.lean`, copyright 2022. This supplies the full Hilbert sum ℓ² structure.
- **Jireh Loreaux**, `Mathlib/Analysis/CStarAlgebra/ContinuousLinearMap.lean`, copyright 2024. This supplies the bounded-operator C*-algebra structure.

These files are Apache-2.0 licensed in the pinned mathlib checkout. Their individual notices remain in the separately fetched source files. Scholarly citations, including mathlib's requested citation, are in [REFERENCES.md](REFERENCES.md).

## Build infrastructure

GitHub CI uses [actions/checkout](https://github.com/actions/checkout) at `v4` and [leanprover/lean-action](https://github.com/leanprover/lean-action) at `v1`. They run as external GitHub Actions and are not included in this source distribution. These action version references are separate from the exact Lean and Lake dependency pins.
