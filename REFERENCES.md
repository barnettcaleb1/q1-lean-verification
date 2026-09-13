# References

## Original question

Nazmul Alam, Joseph Gondek, Mehrdad Kalantar and Randy Pham. **Growth conditions for topological freeness.** [arXiv:2602.15009v2](https://arxiv.org/abs/2602.15009v2), 19 June 2026. The motivating question is Section 3, Question 1; the reduced-norm growth convention is Definition 1. The paper also supplies the mathematical tuple-injection ingredient underlying the conjugacy-growth route; its encoded form is proved in [ConjugacyTuples.lean](Q1/ConjugacyTuples.lean). This repository specifies finite symmetric generation and exact shortest word length explicitly. Attribution to the question's authors is separate from attribution to the verification files.

## Mathematical background

- P. Erdős and R. Rado. **Intersection Theorems for Systems of Sets.** *Journal of the London Mathematical Society* s1-35(1), 85–90 (1960). [DOI: 10.1112/jlms/s1-35.1.85](https://doi.org/10.1112/jlms/s1-35.1.85). Classical sunflower background; the finite combinatorial lemma used here is proved in [Sunflower.lean](Q1/Sunflower.lean).
- P. Hall. **On Representatives of Subsets.** *Journal of the London Mathematical Society* s1-10(1), 26–30 (1935). [DOI: 10.1112/jlms/s1-10.37.26](https://doi.org/10.1112/jlms/s1-10.37.26). The Hall matching theorem used by [MeanFoelner.lean](Q1/MeanFoelner.lean) comes from mathlib.
- James D. Halpern. **Bases in vector spaces and the axiom of choice.** *Proceedings of the American Mathematical Society* 17, 670–673 (1966). [DOI: 10.2307/2035388](https://doi.org/10.2307/2035388). Background cited by mathlib for its compactness extension of Hall's theorem to arbitrarily indexed finite sets.
- Alena Gusakov, Bhavik Mehta and Kyle A. Miller. **Formalizing Hall's Marriage Theorem in Lean.** [arXiv:2101.00127](https://arxiv.org/abs/2101.00127) (2021). Related account of the upstream Hall formalization; the dependency used here is the pinned mathlib source.

These references credit mathematical background and upstream formalization. The Lean build checks the implemented arguments and imported declarations; it does not import papers as axioms. The final direct averaging argument is described in the [theorem guide](docs/THEOREMS.md).

## Proof assistant and library

- Leonardo de Moura and Sebastian Ullrich. **The Lean 4 Theorem Prover and Programming Language.** In *Automated Deduction – CADE 28*, LNCS 12699, 625–635 (2021). [DOI: 10.1007/978-3-030-79876-5_37](https://doi.org/10.1007/978-3-030-79876-5_37). [Official paper](https://lean-lang.org/papers/lean4.pdf).
- The mathlib Community. **The Lean Mathematical Library.** In *Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)* (2020). [DOI: 10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824). This follows the citation requested by the pinned mathlib distribution.

Exact software revisions and dependency notices are in [THIRD_PARTY.md](THIRD_PARTY.md). [CITATION.cff](CITATION.cff) describes this verification artifact itself.
