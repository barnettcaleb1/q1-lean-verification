import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Data.Finsupp.BigOperators

/-! The actual left regular representation on the full complex Hilbert space
`lp (fun _ : G => ℂ) 2`, and its finite coefficient convolution operators.
No finiteness or countability hypothesis on `G` is needed. -/

open scoped ENNReal

noncomputable section

namespace Q1

/-- The full complex square-summable function space on the group. -/
abbrev GroupL2 (G : Type*) := lp (fun _ : G => ℂ) 2

variable {G : Type*} [Group G]

/-- Left translation as a complex linear isometry of the full ℓ² space. -/
noncomputable def leftRegularIsometry (g : G) : GroupL2 G →ₗᵢ[ℂ] GroupL2 G where
  toFun ξ := ⟨fun x => ξ (g⁻¹ * x), by
    apply memℓp_gen
    exact (Equiv.summable_iff (Equiv.mulLeft g⁻¹)).mpr
      ((lp.memℓp ξ).summable (by norm_num))⟩
  map_add' ξ η := by apply lp.ext; rfl
  map_smul' c ξ := by apply lp.ext; rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact (Equiv.mulLeft g⁻¹).tsum_eq (fun x => ‖ξ x‖ ^ (2 : ℝ≥0∞).toReal)

/-- The bounded operator λ(g), with convention λ(g)ξ(x)=ξ(g⁻¹x). -/
noncomputable def leftRegular (g : G) : GroupL2 G →L[ℂ] GroupL2 G :=
  (leftRegularIsometry g).toContinuousLinearMap

@[simp] theorem leftRegular_apply (g : G) (ξ : GroupL2 G) (x : G) :
    leftRegular g ξ x = ξ (g⁻¹ * x) := rfl

@[simp] theorem norm_leftRegular_apply (g : G) (ξ : GroupL2 G) :
    ‖leftRegular g ξ‖ = ‖ξ‖ := (leftRegularIsometry g).norm_map ξ

@[simp] theorem leftRegular_one : leftRegular (1 : G) = ContinuousLinearMap.id ℂ (GroupL2 G) := by
  ext ξ x
  simp

/-- The chosen inverse convention gives λ(gh)=λ(g)∘λ(h). -/
theorem leftRegular_mul (g h : G) :
    leftRegular (g * h) = (leftRegular g).comp (leftRegular h) := by
  ext ξ x
  simp [mul_assoc]

@[simp] theorem leftRegular_single [DecidableEq G] (g h : G) (z : ℂ) :
    leftRegular g (lp.single 2 h z) = lp.single 2 (g * h) z := by
  classical
  apply lp.ext
  funext x
  simp only [leftRegular_apply, lp.single_apply]
  by_cases hx : x = g * h
  · subst x; simp
  · have hi : g⁻¹ * x ≠ h := by
      intro he
      apply hx
      calc x = g * (g⁻¹ * x) := by simp
           _ = g * h := by rw [he]
    simp [Pi.single_eq_of_ne hx, Pi.single_eq_of_ne hi]

@[simp] theorem norm_leftRegular (g : G) : ‖leftRegular g‖ = 1 := by
  classical
  apply le_antisymm
  · exact (leftRegularIsometry g).norm_toContinuousLinearMap_le
  · have h := (leftRegular g).le_opNorm (lp.single 2 (1 : G) (1 : ℂ))
    simpa [norm_leftRegular_apply, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using h

/-- Finite-coefficient left convolution, acting on the whole ℓ²(G). -/
noncomputable def regularConvolution (f : G →₀ ℂ) : GroupL2 G →L[ℂ] GroupL2 G :=
  f.sum fun g z => z • leftRegular g

/-- The exact finite convolution formula, with the left-regular convention. -/
theorem regularConvolution_apply (f : G →₀ ℂ) (ξ : GroupL2 G) (x : G) :
    regularConvolution f ξ x = ∑ g ∈ f.support, f g * ξ (g⁻¹ * x) := by
  classical
  change ((∑ g ∈ f.support, f g • leftRegular g) ξ) x = _
  rw [sum_apply, lp.coeFn_sum, Finset.sum_apply]
  simp only [smul_apply, lp.coeFn_smul, Pi.smul_apply,
    leftRegular_apply, smul_eq_mul]

@[simp] theorem regularConvolution_single (g : G) (z : ℂ) :
    regularConvolution (Finsupp.single g z) = z • leftRegular g := by
  simp [regularConvolution]

@[simp] theorem regularConvolution_zero : regularConvolution (0 : G →₀ ℂ) = 0 := by
  simp [regularConvolution]

/-- The standard ℓ¹ estimate is an operator bound on full ℓ²(G). -/
theorem norm_regularConvolution_le (f : G →₀ ℂ) :
    ‖regularConvolution f‖ ≤ ∑ g ∈ f.support, ‖f g‖ := by
  classical
  calc
    ‖regularConvolution f‖ ≤ ∑ g ∈ f.support, ‖f g • leftRegular g‖ :=
      norm_sum_le _ _
    _ = _ := by simp [norm_smul]

/-- The square-summable vector of a finite coefficient function. -/
noncomputable def coefficientVector (f : G →₀ ℂ) : GroupL2 G := by
  classical
  exact f.sum fun g z => lp.single 2 g z

omit [Group G] in
@[simp] theorem coefficientVector_apply (f : G →₀ ℂ) (x : G) :
    coefficientVector f x = f x := by
  classical
  simp only [coefficientVector, Finsupp.sum, lp.coeFn_sum, Finset.sum_apply,
    lp.single_apply, Finset.sum_pi_single]
  split_ifs with hx
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hx).symm

/-- The coefficient ℓ² norm, distinct from the convolution operator norm. -/
noncomputable def coefficientL2Norm (f : G →₀ ℂ) : ℝ := ‖coefficientVector f‖

omit [Group G] in
/-- Parseval's finite sum identity in the actual ℓ² space. -/
theorem coefficientL2Norm_sq (f : G →₀ ℂ) :
    coefficientL2Norm f ^ 2 = ∑ g ∈ f.support, ‖f g‖ ^ 2 := by
  classical
  simpa [coefficientL2Norm, coefficientVector, Finsupp.sum] using
    lp.norm_sum_single (p := 2) (by norm_num) (fun g => f g) f.support

omit [Group G] in
@[simp] theorem coefficientVector_single [DecidableEq G] (g : G) (z : ℂ) :
    coefficientVector (Finsupp.single g z) = lp.single 2 g z := by
  apply lp.ext
  funext x
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

omit [Group G] in
@[simp] theorem coefficientL2Norm_single (g : G) (z : ℂ) :
    coefficientL2Norm (Finsupp.single g z) = ‖z‖ := by
  classical
  simp [coefficientL2Norm, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

/-- Applying convolution to δ₁ recovers the original coefficient vector. -/
theorem regularConvolution_delta [DecidableEq G] (f : G →₀ ℂ) :
    regularConvolution f (lp.single 2 (1 : G) (1 : ℂ)) = coefficientVector f := by
  apply lp.ext
  funext x
  rw [regularConvolution_apply, coefficientVector_apply]
  calc
    (∑ g ∈ f.support, f g * lp.single (E := fun _ : G => ℂ) 2 (1 : G) (1 : ℂ) (g⁻¹ * x)) =
        ∑ g ∈ f.support, Pi.single g (f g) x := by
      apply Finset.sum_congr rfl
      intro g hg
      by_cases hx : x = g
      · subst x; simp
      · have hi : g⁻¹ * x ≠ 1 := by
          intro hh
          apply hx
          calc x = g * (g⁻¹ * x) := by simp
               _ = g := by rw [hh, mul_one]
        simp only [lp.single_apply, Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hx, mul_zero]
    _ = f x := by
      rw [Finset.sum_pi_single]
      split_ifs with hx
      · rfl
      · exact (Finsupp.notMem_support_iff.mp hx).symm

/-- Testing the regular operator on the unit vector δ₁ gives the ℓ² lower bound. -/
theorem coefficientL2Norm_le_norm_regularConvolution (f : G →₀ ℂ) :
    coefficientL2Norm f ≤ ‖regularConvolution f‖ := by
  classical
  have h := (regularConvolution f).le_opNorm (lp.single 2 (1 : G) (1 : ℂ))
  simpa [regularConvolution_delta, coefficientL2Norm,
    lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)] using h

end Q1

namespace Q1
variable {G : Type*}

@[simp] theorem coefficientVector_zero : coefficientVector (0 : G →₀ ℂ) = 0 := by
  apply lp.ext
  funext x
  simp

theorem coefficientVector_injective : Function.Injective (coefficientVector (G := G)) := by
  intro f h he
  apply Finsupp.ext
  intro x
  have hx := congrArg (fun ξ : GroupL2 G => ξ x) he
  simpa using hx

@[simp] theorem coefficientVector_eq_zero (f : G →₀ ℂ) :
    coefficientVector f = 0 ↔ f = 0 := by
  rw [← coefficientVector_zero, coefficientVector_injective.eq_iff]

@[simp] theorem coefficientL2Norm_zero : coefficientL2Norm (0 : G →₀ ℂ) = 0 := by
  simp [coefficientL2Norm]

theorem coefficientL2Norm_nonneg (f : G →₀ ℂ) : 0 ≤ coefficientL2Norm f := norm_nonneg _

@[simp] theorem coefficientL2Norm_eq_zero (f : G →₀ ℂ) :
    coefficientL2Norm f = 0 ↔ f = 0 := by
  simp [coefficientL2Norm]

theorem coefficientL2Norm_pos (f : G →₀ ℂ) :
    0 < coefficientL2Norm f ↔ f ≠ 0 := by
  simp [coefficientL2Norm]

@[simp] theorem coefficientVector_add (f h : G →₀ ℂ) :
    coefficientVector (f + h) = coefficientVector f + coefficientVector h := by
  apply lp.ext
  funext x
  simp

@[simp] theorem coefficientVector_smul (z : ℂ) (f : G →₀ ℂ) :
    coefficientVector (z • f) = z • coefficientVector f := by
  apply lp.ext
  funext x
  simp

@[simp] theorem coefficientL2Norm_smul (z : ℂ) (f : G →₀ ℂ) :
    coefficientL2Norm (z • f) = ‖z‖ * coefficientL2Norm f := by
  simp [coefficientL2Norm, norm_smul]

variable [Group G]

@[simp] theorem regularConvolution_eq_zero (f : G →₀ ℂ) :
    regularConvolution f = 0 ↔ f = 0 := by
  constructor
  · intro hf
    apply (coefficientL2Norm_eq_zero f).mp
    exact le_antisymm (by simpa [hf] using coefficientL2Norm_le_norm_regularConvolution f)
      (coefficientL2Norm_nonneg f)
  · rintro rfl
    exact regularConvolution_zero

@[simp] theorem regularConvolution_add (f h : G →₀ ℂ) :
    regularConvolution (f + h) = regularConvolution f + regularConvolution h := by
  classical
  exact Finsupp.sum_add_index' (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)

@[simp] theorem regularConvolution_smul (z : ℂ) (f : G →₀ ℂ) :
    regularConvolution (z • f) = z • regularConvolution f := by
  classical
  unfold regularConvolution
  rw [Finsupp.sum_smul_index (h := fun g z => z • leftRegular g) (fun _ => zero_smul ℂ _)]
  simp only [Finsupp.sum, Finset.smul_sum, smul_smul]

end Q1
