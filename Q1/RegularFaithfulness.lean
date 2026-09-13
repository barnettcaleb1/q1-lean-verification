import Q1.ReducedAlgebra

/-! Right translations commute with the reduced algebra. Consequently the
identity vector is separating, and its vector functional is faithful on a*a. -/

noncomputable section
open scoped ENNReal InnerProduct
namespace Q1
variable {G : Type*} [Group G]

/-- Right regular translation, with convention ρ(g)ξ(x)=ξ(xg). -/
def rightRegularIsometry (g : G) : GroupL2 G →ₗᵢ[ℂ] GroupL2 G where
  toFun ξ := ⟨fun x => ξ (x * g), by
    apply memℓp_gen
    exact (Equiv.summable_iff (Equiv.mulRight g)).mpr
      ((lp.memℓp ξ).summable (by norm_num))⟩
  map_add' ξ η := by apply lp.ext; rfl
  map_smul' c ξ := by apply lp.ext; rfl
  norm_map' ξ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact (Equiv.mulRight g).tsum_eq (fun x => ‖ξ x‖ ^ (2 : ℝ≥0∞).toReal)

def rightRegular (g : G) : RegularOperator G :=
  (rightRegularIsometry g).toContinuousLinearMap

@[simp] theorem rightRegular_apply (g : G) (ξ : GroupL2 G) (x : G) :
    rightRegular g ξ x = ξ (x * g) := rfl

@[simp] theorem rightRegular_single [DecidableEq G] (g h : G) (z : ℂ) :
    rightRegular g (lp.single 2 h z) = lp.single 2 (h * g⁻¹) z := by
  classical
  apply lp.ext
  funext x
  simp only [rightRegular_apply, lp.single_apply]
  by_cases hx : x = h * g⁻¹
  · subst x; simp
  · have hi : x * g ≠ h := by
      intro he
      apply hx
      calc x = (x * g) * g⁻¹ := by simp
           _ = h * g⁻¹ := by rw [he]
    simp [Pi.single_eq_of_ne hx, Pi.single_eq_of_ne hi]

theorem leftRegular_commute_rightRegular (g h : G) :
    leftRegular g * rightRegular h = rightRegular h * leftRegular g := by
  ext ξ x
  simp [mul_assoc]

theorem regularConvolution_commute_rightRegular (f : G →₀ ℂ) (g : G) :
    regularConvolution f * rightRegular g = rightRegular g * regularConvolution f := by
  classical
  simp only [regularConvolution, Finsupp.sum, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, leftRegular_commute_rightRegular]

/-- Commutation passes to the operator-norm closure. -/
theorem reducedGroupAlgebra_commute_rightRegular {a : RegularOperator G}
    (ha : a ∈ reducedGroupAlgebra) (g : G) :
    a * rightRegular g = rightRegular g * a := by
  have hc : IsClosed {b : RegularOperator G | b * rightRegular g = rightRegular g * b} :=
    isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)
  apply closure_minimal (t := {b : RegularOperator G | b * rightRegular g = rightRegular g * b})
    (s := Set.range (regularConvolution (G := G))) ?_ hc
    ((mem_reducedGroupAlgebra_iff a).mp ha)
  rintro _ ⟨f, rfl⟩
  exact regularConvolution_commute_rightRegular f g

/-- The unit point mass δ₁ in the full complex Hilbert space. -/
def groupIdentityVector : GroupL2 G := by
  classical
  exact lp.single 2 (1 : G) (1 : ℂ)

@[simp] theorem norm_groupIdentityVector : ‖groupIdentityVector (G := G)‖ = 1 := by
  classical
  simp [groupIdentityVector, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

/-- The identity vector separates operators of the reduced algebra. -/
theorem reducedGroupAlgebra_eq_zero_of_delta {a : RegularOperator G}
    (ha : a ∈ reducedGroupAlgebra) (hδ : a groupIdentityVector = 0) : a = 0 := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro g
  apply ContinuousLinearMap.ext
  intro z
  change a (lp.single 2 g z) = 0
  have he : lp.single 2 g z = z • rightRegular g⁻¹ groupIdentityVector := by
    simp [groupIdentityVector, ← lp.single_smul]
  rw [he, map_smul]
  have hc := congrArg (fun b : RegularOperator G => b groupIdentityVector)
    (reducedGroupAlgebra_commute_rightRegular ha g⁻¹)
  change a (rightRegular g⁻¹ groupIdentityVector) = rightRegular g⁻¹ (a groupIdentityVector) at hc
  rw [hc, hδ, map_zero, smul_zero]

/-- The continuous identity-vector functional on all bounded regular-space operators. -/
def regularVectorState : RegularOperator G →L[ℂ] ℂ :=
  (innerSL ℂ (groupIdentityVector (G := G))).comp
    (ContinuousLinearMap.apply ℂ (GroupL2 G) groupIdentityVector)

@[simp] theorem regularVectorState_apply (a : RegularOperator G) :
    regularVectorState a = inner ℂ groupIdentityVector (a groupIdentityVector) := rfl

theorem norm_regularVectorState_apply_le (a : RegularOperator G) :
    ‖regularVectorState a‖ ≤ ‖a‖ := by
  calc
    ‖regularVectorState a‖ ≤ ‖groupIdentityVector (G := G)‖ * ‖a groupIdentityVector‖ :=
      by
        rw [regularVectorState_apply]
        exact norm_inner_le_norm _ _
    _ ≤ ‖groupIdentityVector (G := G)‖ * (‖a‖ * ‖groupIdentityVector (G := G)‖) := by
      gcongr
      exact a.le_opNorm _
    _ = ‖a‖ := by simp

@[simp] theorem regularVectorState_one : regularVectorState (1 : RegularOperator G) = 1 := by
  simp [regularVectorState_apply, inner_self_eq_norm_sq_to_K]

@[simp] theorem regularVectorState_regularConvolution (f : G →₀ ℂ) :
    regularVectorState (regularConvolution f) = f 1 := by
  classical
  simp [regularVectorState_apply, groupIdentityVector, regularConvolution_delta,
    lp.inner_single_left]

theorem regularVectorState_star_mul_self (a : RegularOperator G) :
    regularVectorState (star a * a) = (‖a groupIdentityVector‖ ^ 2 : ℂ) := by
  rw [regularVectorState_apply, mul_apply_eq_comp,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_self_eq_norm_sq_to_K]
  rfl

/-- The canonical vector state restricted to the actual reduced C*-algebra. -/
def reducedVectorState : ReducedGroupCStarAlgebra G →L[ℂ] ℂ :=
  regularVectorState.comp (reducedGroupAlgebra.toSubalgebra.toSubmodule.subtypeL)

@[simp] theorem reducedVectorState_apply (a : ReducedGroupCStarAlgebra G) :
    reducedVectorState a = regularVectorState (a : RegularOperator G) := rfl

@[simp] theorem reducedVectorState_reducedPolynomial (f : G →₀ ℂ) :
    reducedVectorState (reducedPolynomial f) = f 1 :=
  regularVectorState_regularConvolution f

/-- Faithfulness is proved from right-translation commutation, not assumed as a trace criterion. -/
theorem reducedVectorState_faithful (a : ReducedGroupCStarAlgebra G) (ha : a ≠ 0) :
    reducedVectorState (star a * a) ≠ 0 := by
  change regularVectorState (star (a : RegularOperator G) * (a : RegularOperator G)) ≠ 0
  rw [regularVectorState_star_mul_self]
  have hδ : (a : RegularOperator G) groupIdentityVector ≠ 0 := by
    intro h
    apply ha
    exact Subtype.ext (reducedGroupAlgebra_eq_zero_of_delta a.property h)
  exact pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.mpr hδ)

end Q1
