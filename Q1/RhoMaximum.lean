import Q1.ReducedNorm
import Mathlib.Data.Finsupp.Indicator
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

/-! Maximum attainment for the actual reduced regular norm on a nonempty
finite coefficient set. The parameter space is the finite-dimensional complex
space `B → ℂ`; no truncation of the full ℓ² representation is used. -/

noncomputable section

open scoped ENNReal

namespace Q1

variable {G : Type*}

/-- Extend finite coordinates by zero to a finitely supported coefficient. -/
def ballCoefficient (B : Finset G) (u : B → ℂ) : G →₀ ℂ :=
  Finsupp.indicator B (fun g hg => u ⟨g, hg⟩)

theorem ballCoefficient_support (B : Finset G) (u : B → ℂ) :
    (ballCoefficient B u).support ⊆ B := Finsupp.support_indicator_subset B _

@[simp] theorem ballCoefficient_apply (B : Finset G) (u : B → ℂ) (g : B) :
    ballCoefficient B u g = u g := Finsupp.indicator_of_mem g.property _

theorem ballCoefficient_restrict (B : Finset G) (f : G →₀ ℂ) (hf : f.support ⊆ B) :
    ballCoefficient B (fun g => f g) = f :=
  ((Finsupp.eq_indicator_self_iff B).mpr hf).symm

@[simp] theorem ballCoefficient_add (B : Finset G) (u v : B → ℂ) :
    ballCoefficient B (u + v) = ballCoefficient B u + ballCoefficient B v := by
  classical
  ext g
  by_cases hg : g ∈ B <;> simp [ballCoefficient, Finsupp.indicator_apply, hg]

@[simp] theorem ballCoefficient_smul (B : Finset G) (z : ℂ) (u : B → ℂ) :
    ballCoefficient B (z • u) = z • ballCoefficient B u := by
  classical
  ext g
  by_cases hg : g ∈ B <;> simp [ballCoefficient, Finsupp.indicator_apply, hg]

/-- The full ℓ² coefficient vector depends linearly on the finite coordinates. -/
def ballCoefficientVector (B : Finset G) : (B → ℂ) →ₗ[ℂ] GroupL2 G where
  toFun u := coefficientVector (ballCoefficient B u)
  map_add' u v := by simp
  map_smul' z u := by simp

theorem continuous_ballCoefficientNorm (B : Finset G) :
    Continuous (fun u : B → ℂ => coefficientL2Norm (ballCoefficient B u)) :=
  (ballCoefficientVector B).continuous_of_finiteDimensional.norm

/-- Every finite coordinate is bounded by the counting-measure coefficient ℓ² norm. -/
theorem norm_coordinate_le_coefficientL2Norm (B : Finset G) (u : B → ℂ) (g : B) :
    ‖u g‖ ≤ coefficientL2Norm (ballCoefficient B u) := by
  simpa [coefficientL2Norm] using
    lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (coefficientVector (ballCoefficient B u)) (g : G)

/-- The coefficient unit sphere is compact in finite coordinate space. -/
theorem isCompact_ballCoefficient_unitSphere (B : Finset G) :
    IsCompact {u : B → ℂ | coefficientL2Norm (ballCoefficient B u) = 1} := by
  apply (isCompact_closedBall (0 : B → ℂ) 1).of_isClosed_subset
    (isClosed_eq (continuous_ballCoefficientNorm B) continuous_const)
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro g
  exact (norm_coordinate_le_coefficientL2Norm B u g).trans_eq hu

variable [Group G]

/-- Finite coefficient coordinates yield operators on the full complex ℓ² space. -/
def ballRegularConvolution (B : Finset G) :
    (B → ℂ) →ₗ[ℂ] (GroupL2 G →L[ℂ] GroupL2 G) where
  toFun u := regularConvolution (ballCoefficient B u)
  map_add' u v := by simp
  map_smul' z u := by simp

theorem continuous_ballRegularConvolution_norm (B : Finset G) :
    Continuous (fun u : B → ℂ => ‖regularConvolution (ballCoefficient B u)‖) :=
  (ballRegularConvolution B).continuous_of_finiteDimensional.norm

/-- Rescale a finite coefficient to coefficient ℓ² norm one when it is nonzero. -/
def unitCoefficient (f : G →₀ ℂ) : G →₀ ℂ :=
  (coefficientL2Norm f : ℂ)⁻¹ • f

omit [Group G] in
theorem unitCoefficient_support (f : G →₀ ℂ) :
    (unitCoefficient f).support ⊆ f.support := Finsupp.support_smul

omit [Group G] in
theorem norm_inverse_coefficientL2Norm (f : G →₀ ℂ) :
    ‖(coefficientL2Norm f : ℂ)⁻¹‖ = (coefficientL2Norm f)⁻¹ := by
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (coefficientL2Norm_nonneg f)]

omit [Group G] in
theorem coefficientL2Norm_unitCoefficient (f : G →₀ ℂ) (hf : f ≠ 0) :
    coefficientL2Norm (unitCoefficient f) = 1 := by
  rw [unitCoefficient, coefficientL2Norm_smul, norm_inverse_coefficientL2Norm,
    inv_mul_cancel₀ (ne_of_gt ((coefficientL2Norm_pos f).mpr hf))]

theorem norm_regularConvolution_unitCoefficient (f : G →₀ ℂ) :
    ‖regularConvolution (unitCoefficient f)‖ = reducedRatio f := by
  rw [unitCoefficient, regularConvolution_smul, norm_smul,
    norm_inverse_coefficientL2Norm, reducedRatio, div_eq_mul_inv, mul_comm]

omit [Group G] in
/-- A nonempty finite support set admits a coefficient unit vector. -/
theorem ballCoefficient_unitSphere_nonempty (B : Finset G) (hB : B.Nonempty) :
    ({u : B → ℂ | coefficientL2Norm (ballCoefficient B u) = 1} : Set (B → ℂ)).Nonempty := by
  classical
  obtain ⟨g, hg⟩ := hB
  let f : G →₀ ℂ := Finsupp.single g 1
  have hs : f.support ⊆ B := by simpa [f] using hg
  refine ⟨fun x => f x, ?_⟩
  change coefficientL2Norm (ballCoefficient B (fun x => f x)) = 1
  rw [ballCoefficient_restrict B f hs]
  simp [f]

/-- The exact reduced-ball supremum is attained by a coefficient of ℓ² norm one. -/
theorem reducedBallRho_attained (B : Finset G) (hB : B.Nonempty) :
    ∃ f : G →₀ ℂ, f.support ⊆ B ∧ coefficientL2Norm f = 1 ∧
      ‖regularConvolution f‖ = reducedBallRho B := by
  classical
  obtain ⟨u, hu, hmax⟩ := (isCompact_ballCoefficient_unitSphere B).exists_isMaxOn
    (ballCoefficient_unitSphere_nonempty B hB)
    (continuous_ballRegularConvolution_norm B).continuousOn
  let f := ballCoefficient B u
  have hf : f.support ⊆ B := ballCoefficient_support B u
  have hunit : coefficientL2Norm f = 1 := hu
  refine ⟨f, hf, hunit, le_antisymm ?_ ?_⟩
  · simpa [reducedRatio, hunit] using reducedRatio_le_rho B f hf
  · apply csSup_le (reducedRatios_nonempty B)
    rintro x ⟨a, ha, rfl⟩
    by_cases hz : a = 0
    · simp only [hz, reducedRatio, regularConvolution_zero, norm_zero, zero_div]
      exact norm_nonneg _
    · have hs : (unitCoefficient a).support ⊆ B := (unitCoefficient_support a).trans ha
      let v : B → ℂ := fun g => unitCoefficient a g
      have hv : ballCoefficient B v = unitCoefficient a := ballCoefficient_restrict B _ hs
      have hvs : coefficientL2Norm (ballCoefficient B v) = 1 := by
        rw [hv]
        exact coefficientL2Norm_unitCoefficient a hz
      have hle : ‖regularConvolution (ballCoefficient B v)‖ ≤
          ‖regularConvolution f‖ := hmax hvs
      rw [hv, norm_regularConvolution_unitCoefficient] at hle
      exact hle

/-- The maximum equals the original nonzero-coefficient ratio, with unit denominator. -/
theorem reducedBallRho_attained_ratio (B : Finset G) (hB : B.Nonempty) :
    ∃ f : G →₀ ℂ, f ≠ 0 ∧ f.support ⊆ B ∧ coefficientL2Norm f = 1 ∧
      reducedRatio f = reducedBallRho B := by
  obtain ⟨f, hf, hunit, hnorm⟩ := reducedBallRho_attained B hB
  refine ⟨f, ?_, hf, hunit, ?_⟩
  · intro hz
    simp [hz] at hunit
  · simpa [reducedRatio, hunit] using hnorm

/-- Thus rho is the greatest member of precisely the original nonzero ratio set. -/
theorem reducedBallRho_isGreatest (B : Finset G) (hB : B.Nonempty) :
    IsGreatest (nonzeroReducedRatios B) (reducedBallRho B) := by
  obtain ⟨f, hne, hf, _, heq⟩ := reducedBallRho_attained_ratio B hB
  refine ⟨⟨f, hne, hf, heq⟩, ?_⟩
  rintro x ⟨a, _, ha, rfl⟩
  exact reducedRatio_le_rho B a ha

/-- Maximum attainment holds at every radius of the specified ambient length. -/
theorem reducedRho_attained (L : LengthBall G) (r : ℕ) :
    ∃ f : G →₀ ℂ, f ≠ 0 ∧ f.support ⊆ L.ball r ∧ coefficientL2Norm f = 1 ∧
      reducedRatio f = reducedRho L r :=
  reducedBallRho_attained_ratio (L.ball r)
    ⟨1, (L.mem_ball 1 r).mpr (by simp [L.length_one])⟩

/-- Exact finite symmetric generating-set specialization, at every natural radius. -/
theorem reducedRho_wordLength_attained (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤) (r : ℕ) :
    ∃ f : G →₀ ℂ, f ≠ 0 ∧ f.support ⊆ wordBall S r ∧ coefficientL2Norm f = 1 ∧
      reducedRatio f = reducedRho (wordLengthBall S hsym hgen) r :=
  reducedRho_attained (wordLengthBall S hsym hgen) r

end Q1
