import Q1.ReducedNorm
import Q1.FoelnerOperator
import Q1.MeanFoelner
import Q1.RadicalGrowth
import Mathlib.Data.Finsupp.Indicator

/-! The amenable subgroup-volume estimate in the actual reduced regular norm
and the same ambient length used by the confinement packing theorem. -/

noncomputable section

namespace Q1

variable {G : Type*} [Group G]

/-- The finitely supported complex indicator, with every coefficient equal to
one on A and zero elsewhere. -/
def indicatorCoefficient (A : Finset G) : G →₀ ℂ :=
  Finsupp.indicator A (fun _ _ => 1)

omit [Group G] in
@[simp] theorem indicatorCoefficient_apply [DecidableEq G] (A : Finset G) (g : G) :
    indicatorCoefficient A g = if g ∈ A then 1 else 0 := by
  simp [indicatorCoefficient, Finsupp.indicator_apply]

omit [Group G] in
@[simp] theorem support_indicatorCoefficient (A : Finset G) :
    (indicatorCoefficient A).support = A := by
  classical
  ext g
  simp [Finsupp.mem_support_iff, indicatorCoefficient_apply]

omit [Group G] in
theorem coefficientL2Norm_indicator_sq (A : Finset G) :
    coefficientL2Norm (indicatorCoefficient A) ^ 2 = (A.card : ℝ) := by
  classical
  rw [coefficientL2Norm_sq, support_indicatorCoefficient]
  calc
    (∑ g ∈ A, ‖indicatorCoefficient A g‖ ^ 2) = ∑ _g ∈ A, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro g hg
      simp [hg]
    _ = _ := by simp

omit [Group G] in
theorem coefficientL2Norm_indicator (A : Finset G) :
    coefficientL2Norm (indicatorCoefficient A) = Real.sqrt (A.card : ℝ) := by
  rw [← coefficientL2Norm_indicator_sq, Real.sqrt_sq (coefficientL2Norm_nonneg _)]

theorem regularConvolution_indicator (A : Finset G) :
    regularConvolution (indicatorCoefficient A) = ∑ g ∈ A, leftRegular g := by
  classical
  change (∑ g ∈ (indicatorCoefficient A).support,
    indicatorCoefficient A g • leftRegular g) = _
  rw [support_indicatorCoefficient]
  apply Finset.sum_congr rfl
  intro g hg
  simp [hg]

/-- Amenability in the exact invariant-set-probability convention gives the
full positive mass as an actual ambient reduced operator norm. -/
theorem norm_regularConvolution_indicator_of_hasInvariantMean
    (H : Subgroup G) (hH : HasInvariantMean H) (A : Finset G)
    (hA : ∀ g ∈ A, g ∈ H) :
    ‖regularConvolution (indicatorCoefficient A)‖ = (A.card : ℝ) := by
  rw [regularConvolution_indicator]
  exact norm_sum_leftRegular_eq_card_of_finiteFoelner H
    (finiteFoelner_of_hasInvariantMean hH) A hA

/-- Every finite amenable-subgroup subset inside B is bounded by the square of
the actual reduced-norm growth constant on B. -/
theorem amenable_subset_card_le_reducedBallRho_sq
    (H : Subgroup G) (hH : HasInvariantMean H) (A B : Finset G)
    (hA : ∀ g ∈ A, g ∈ H) (hAB : A ⊆ B) :
    (A.card : ℝ) ≤ reducedBallRho B ^ 2 := by
  have hbound := norm_regularConvolution_le_rho_mul B (indicatorCoefficient A)
    (by simpa using hAB)
  rw [norm_regularConvolution_indicator_of_hasInvariantMean H hH A hA,
    coefficientL2Norm_indicator] at hbound
  have hc : 0 ≤ (A.card : ℝ) := Nat.cast_nonneg _
  have hs := Real.sq_sqrt hc
  have hρ := reducedBallRho_nonneg B
  have hroot := Real.sqrt_nonneg (A.card : ℝ)
  nlinarith [sq_nonneg (reducedBallRho B - Real.sqrt (A.card : ℝ))]

/-- The amenable subgroup-volume estimate uses the original ambient ball,
not the intrinsic subgroup metric. No volume hypothesis remains. -/
theorem amenable_subgroupBall_card_le_reducedRho_sq [DecidableEq G]
    (L : LengthBall G) (H : Subgroup G) (hH : HasInvariantMean H) (r : ℕ) :
    ((subgroupBall L H r).card : ℝ) ≤ reducedRho L r ^ 2 := by
  classical
  apply amenable_subset_card_le_reducedBallRho_sq H hH
  · intro g hg
    exact (Finset.mem_filter.mp hg).2
  · exact Finset.filter_subset _ _

/-- Ordinary SRD, trivial radical and amenability rule out actual finite
nonidentity confinement. The nonsimplicity-to-confinement bridge is still separate. -/
theorem no_amenable_confined_subgroup_of_reducedSRD [DecidableEq G]
    (L : LengthBall G) (hR : AmenableNormalCover (⊥ : Subgroup G))
    (hSRD : ReducedSRD L) (H : Subgroup G) (hH : HasInvariantMean H)
    (P : Finset G) (hP : 1 ∉ P) (hconf : ConfinedBy H P) : False :=
  no_confined_subgroup_of_trivial_radical_srd_volume L hR H P hP hconf
    (reducedRho L) (reducedRho_nonneg L) ((reducedSRD_iff_ordinarySRD L).mp hSRD)
    (amenable_subgroupBall_card_le_reducedRho_sq L H hH)

/-- The actual polynomial RD result is a separate corollary. -/
theorem no_amenable_confined_subgroup_of_reducedRD [DecidableEq G]
    (L : LengthBall G) (hR : AmenableNormalCover (⊥ : Subgroup G))
    (hRD : ReducedRD L) (H : Subgroup G) (hH : HasInvariantMean H)
    (P : Finset G) (hP : 1 ∉ P) (hconf : ConfinedBy H P) : False :=
  no_amenable_confined_subgroup_of_reducedSRD L hR hRD.subrapid H hH P hP hconf

/-- The exact finite symmetric shortest-word-length SRD specialization, with
trivial radical supplied by its full defining properties. -/
theorem no_amenable_confined_subgroup_word_srd [DecidableEq G]
    (S : Finset G) (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hR : IsAmenableRadical (⊥ : Subgroup G))
    (hSRD : ReducedSRD (wordLengthBall S hsym hgen))
    (H : Subgroup G) (hH : HasInvariantMean H)
    (P : Finset G) (hP : 1 ∉ P) (hconf : ConfinedBy H P) : False :=
  no_amenable_confined_subgroup_of_reducedSRD (wordLengthBall S hsym hgen)
    hR.maximal hSRD H hH P hP hconf

/-- The separate actual word-length RD specialization. -/
theorem no_amenable_confined_subgroup_word_rd [DecidableEq G]
    (S : Finset G) (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hR : IsAmenableRadical (⊥ : Subgroup G))
    (hRD : ReducedRD (wordLengthBall S hsym hgen))
    (H : Subgroup G) (hH : HasInvariantMean H)
    (P : Finset G) (hP : 1 ∉ P) (hconf : ConfinedBy H P) : False :=
  no_amenable_confined_subgroup_word_srd S hsym hgen hR hRD.subrapid H hH P hP hconf

end Q1
