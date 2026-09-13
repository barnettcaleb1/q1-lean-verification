# Statements and proof correspondence

## Group, length and norm

Let `G` be a discrete group, with a specified finite symmetric generating set `S`. Symmetry means that `s ∈ S` implies `s⁻¹ ∈ S`; generation means `Subgroup.closure (S : Set G) = ⊤`. The length `wordLengthBall S hsym hgen` is the shortest length of an `S`-word representing an element. Its closed ball `B_S(r)` has natural radius `r` and is finite. Intermediate results allow a `LengthBall` with explicit group-length laws and finite exact balls.

The Hilbert space is the full complex counting-measure space ℓ²(G), implemented as `lp (fun _ : G => ℂ) 2`. For `g ∈ G`, left translation is λ(g)ξ(x) = ξ(g⁻¹x). For a finitely supported complex function `f`, set λ(f) = Σ_g f(g)λ(g) and ‖f‖₂ = (Σ_g |f(g)|²)^(1/2). All operator norms are bounded-operator norms on this full Hilbert space.

For every natural radius `r`, the function in the hypotheses is

```text
ρ_S(r) = sup { ‖λ(f)‖ / ‖f‖₂ : f ≠ 0 and support(f) ⊆ B_S(r) }.
```

[ReducedNorm.lean](../Q1/ReducedNorm.lean) defines `reducedRho` and proves agreement with this nonzero supremum. [RhoMaximum.lean](../Q1/RhoMaximum.lean) proves that a maximum is attained on the finite coefficient unit sphere. The operator space remains infinite dimensional when G is infinite.

Amenability means the existence of an ENNReal-valued, left-invariant, finitely additive probability on **all subsets**. `IsAmenableRadical (⊥ : Subgroup G)` says the trivial subgroup is normal and amenable and contains every normal amenable subgroup. The equivalence with `AmenableNormalCover ⊥` is proved as `isAmenableRadical_bot_iff` in [RadicalGrowth.lean](../Q1/RadicalGrowth.lean).

## Q1-SRD

`Q1.q1_srd` assumes the preceding finite symmetric generating set, trivial amenable radical, and `ReducedSRD (wordLengthBall S hsym hgen)`. This is the ordinary full-sequence limit

```text
log(ρ_S(n)) / n → 0  as n → ∞ through ℕ.
```

It concludes `CStarSimple (ReducedGroupCStarAlgebra G)`. The hypothesis is an ordinary limit, not merely a liminf or a subsequence condition. The value assigned to division at radius zero does not affect the limit.

## Q1-RD

`Q1.q1_rd` has the same generating-set and radical hypotheses, with `ReducedRD` in place of `ReducedSRD`:

```text
∃ C ∈ ℝ, C > 0, ∃ d ∈ ℝ, d ≥ 0,
  ∀ r ∈ ℕ, ρ_S(r) ≤ C (1 + r)^d.
```

It concludes the same simplicity statement. The polynomial-bound-to-ordinary-SRD implication is proved as `ReducedRD.subrapid`; the two final declarations remain separate.

## Meaning of the conclusion

`ReducedGroupCStarAlgebra G` is the operator-norm closure of the finite complex span of λ(G) inside B(ℓ²(G)), implemented as a star subalgebra with inherited operations and norm. Completeness, nontriviality and the C*-algebra structure are instantiated in [ReducedAlgebra.lean](../Q1/ReducedAlgebra.lean).

`CStarSimple A` means that **every two-sided ideal whose underlying set is closed in the norm topology is either the zero ideal or the whole algebra**. See [AveragingSimplicity.lean](../Q1/AveragingSimplicity.lean). This is a statement about actual ideals of the completed algebra.

## Proof route

1. Finite combinatorics, amenability and the growth hypothesis give exponential growth of rooted conjugacy orbits when the amenable radical is trivial. The Følner-to-invariant-mean bridge uses mathlib; the reverse bridge is proved here using Hall's theorem.
2. Sunflower packing turns this into arbitrarily many pairwise disjoint conjugates of a fixed finite subset of G ∖ {1}, using conjugators of length O(log N). The same conjugators work for the whole finite set.
3. The reduced operator norm of an average is bounded by ρ(2R(N) + ℓ) / √N, times the fixed coefficient ℓ¹ norm. Ordinary SRD makes this bound tend to zero. This proves averaging toward the identity coefficient for every finite convolution operator.
4. Norm density extends averaging to the completed reduced algebra. Right translations commute with this algebra; the density of point masses in ℓ²(G) makes the identity-vector functional faithful on a*a.
5. For a nonzero element a of a two-sided ideal, average a*a sufficiently close to its nonzero scalar identity coefficient. After scalar normalization the ideal contains an element at distance less than 1 from the unit, hence an invertible element and therefore the whole algebra.

The final route is a direct averaging proof. It has no assumed C*-simplicity criterion, subgroup-volume bound, averaging property or faithful-state bridge. Their needed components are proved in the imported modules. The classical and library sources used along the route are listed in [REFERENCES.md](../REFERENCES.md).

## Reading order

| Subject | Main modules |
| --- | --- |
| Group action and finite packing | `Action`, `Displacement`, `Sunflower`, `PackingObstruction`, `ConjugacyPackingObstruction` |
| Lengths and growth | `WordLength`, `GrowthPacking`, `Asymptotic`, `LogSRD` |
| Full regular representation and reduced norm | `Coefficients`, `RegularRepresentation`, `FiniteNormBounds`, `ReducedNorm`, `RhoMaximum` |
| Amenability and radical growth | `FoelnerLocal`, `FoelnerCommutative`, `FoelnerExtension`, `FoelnerMean`, `MeanFoelner`, `FoelnerOperator`, `FoelnerGrowth`, `NormalClosureWitness`, `SubgroupVolume`, `RadicalCover`, `RadicalGrowth` |
| Conjugacy estimates | `Conjugation`, `ConjugacyTuples`, `ConjugacyGrowthNumeric`, `ConjugacyGrowth` |
| Completed algebra and final proof | `ReducedAlgebra`, `RegularFaithfulness`, `AveragingSimplicity`, `PackedAveraging`, `FullSimplicity` |

The 34 proof modules are preserved from the verified source snapshot. Some comments refer to intermediate development stages, including an internal batch label in `Displacement.lean`; they are historical comments, and no external development files are required to build this repository. The current complete entry point is [Q1.lean](../Q1.lean).
