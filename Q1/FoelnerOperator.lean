import Q1.FoelnerGrowth
import Q1.RegularRepresentation

/-! Finite Følner sets and actual left-regular operator norms on complex `lp`.
The finite Følner hypothesis remains explicit throughout. -/

noncomputable section

namespace Q1

open scoped BigOperators

variable {G : Type*}

local instance : DecidableEq G := Classical.decEq G

/-- The unnormalized finite-set indicator in ambient complex square-summable space. -/
noncomputable def indicatorVector (F : Finset G) : GroupL2 G := by
  classical
  exact ∑ x ∈ F, lp.single 2 x (1 : ℂ)

@[simp] theorem indicatorVector_apply (F : Finset G) (x : G) :
    indicatorVector F x = if x ∈ F then 1 else 0 := by
  classical
  simp only [indicatorVector, lp.coeFn_sum, lp.coeFn_single, Finset.sum_apply,
    Finset.sum_pi_single]

/-- Pairing with an indicator is a genuine finite coordinate sum. -/
theorem inner_indicatorVector_left (F : Finset G) (ξ : GroupL2 G) :
    inner ℂ (indicatorVector F) ξ = ∑ x ∈ F, ξ x := by
  classical
  simp [indicatorVector, sum_inner, lp.inner_single_left]

/-- The ambient Hilbert norm has exactly the counting-measure normalization. -/
theorem indicatorVector_norm_sq (F : Finset G) : ‖indicatorVector F‖ ^ 2 = (F.card : ℝ) := by
  classical
  have h : inner ℂ (indicatorVector F) (indicatorVector F) = (F.card : ℂ) := by
    rw [inner_indicatorVector_left]
    simp
  calc
    ‖indicatorVector F‖ ^ 2 = (inner ℂ (indicatorVector F) (indicatorVector F)).re :=
      norm_sq_eq_re_inner (𝕜 := ℂ) (indicatorVector F)
    _ = (F.card : ℝ) := by rw [h]; simp

variable [Group G]

/-- The coordinate condition in a left-translated finite set. -/
theorem mem_leftTranslate_iff_inv_mul (g x : G) (F : Finset G) :
    x ∈ leftTranslate g F ↔ g⁻¹ * x ∈ F := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨g⁻¹ * x, hx, by simp⟩

/-- The indicator matrix coefficient counts an actual intersection. -/
theorem inner_indicatorVector_leftRegular (g : G) (F : Finset G) :
    inner ℂ (indicatorVector F) (leftRegular g (indicatorVector F)) =
      ((F ∩ leftTranslate g F).card : ℂ) := by
  classical
  rw [inner_indicatorVector_left]
  simp only [leftRegular_apply, indicatorVector_apply]
  simp_rw [← mem_leftTranslate_iff_inv_mul]
  rw [← Finset.sum_filter]
  simp [Finset.filter_mem_eq_inter]

/-- Matrix-coefficient mass equals total mass minus the one-sided boundary. -/
theorem re_inner_indicatorVector_leftRegular (g : G) (F : Finset G) :
    (inner ℂ (indicatorVector F) (leftRegular g (indicatorVector F))).re =
      (F.card : ℝ) - (translateBoundary g F).card := by
  classical
  rw [inner_indicatorVector_leftRegular]
  simp only [Complex.natCast_re]
  have hc := Finset.card_sdiff_add_card_inter (leftTranslate g F) F
  have ht : (leftTranslate g F).card = F.card :=
    Finset.card_image_of_injective F (mul_right_injective g)
  rw [Finset.inter_comm, ht] at hc
  have hcr : ((translateBoundary g F).card : ℝ) + (F ∩ leftTranslate g F).card = F.card := by
    exact_mod_cast hc
  linarith

/-- Injective group homomorphisms preserve finite translated boundary sizes. -/
theorem translateBoundary_image_card {K : Type*} [Group K]
    (φ : K →* G) (hφ : Function.Injective φ) (g : K) (F : Finset K) :
    (translateBoundary (φ g) (F.image φ)).card = (translateBoundary g F).card := by
  classical
  have ht : leftTranslate (φ g) (F.image φ) = (leftTranslate g F).image φ := by
    simp only [leftTranslate, Finset.image_image, Function.comp_def, map_mul]
  have hc := Finset.card_image_of_injective (translateBoundary g F) hφ
  simpa only [translateBoundary, Finset.image_sdiff _ _ hφ, ← ht] using hc

/-- A subgroup Følner set is realized in the ambient group with the same sizes. -/
theorem exists_ambient_foelner_set (H : Subgroup G) (hH : FiniteFoelner H)
    (A : Finset G) (hA : ∀ g ∈ A, g ∈ H) (ε : ℝ) (hε : 0 < ε) :
    ∃ F : Finset G, F.Nonempty ∧
      ∀ g ∈ A, ((translateBoundary g F).card : ℝ) ≤ ε * F.card := by
  classical
  let K : Finset H := A.subtype (· ∈ H)
  obtain ⟨F, hF, hbd⟩ := hH K ε hε
  refine ⟨F.image H.subtype, hF.image _, ?_⟩
  intro g hg
  let a : H := ⟨g, hA g hg⟩
  have ha : a ∈ K := by simpa [K] using hg
  have hh := hbd a ha
  have he := translateBoundary_image_card H.subtype Subtype.val_injective a F
  change (translateBoundary g (F.image H.subtype)).card = _ at he
  have hc : (F.image H.subtype).card = F.card :=
    Finset.card_image_of_injective F (show Function.Injective H.subtype from Subtype.val_injective)
  rw [he, hc]
  exact hh

/-- The triangle inequality gives the exact cardinal upper bound. -/
theorem norm_sum_leftRegular_le_card (A : Finset G) :
    ‖∑ g ∈ A, leftRegular g‖ ≤ (A.card : ℝ) := by
  classical
  calc
    _ ≤ ∑ g ∈ A, ‖leftRegular g‖ := norm_sum_le _ _
    _ = _ := by simp

/-- A finite boundary estimate gives a lower bound in the actual ambient
operator norm; indicators are unnormalized and the cardinal factor cancels. -/
theorem card_mul_one_sub_le_norm_sum_leftRegular_of_boundary
    (A F : Finset G) (hF : F.Nonempty) (ε : ℝ)
    (hbd : ∀ g ∈ A, ((translateBoundary g F).card : ℝ) ≤ ε * F.card) :
    (A.card : ℝ) * (1 - ε) ≤ ‖∑ g ∈ A, leftRegular g‖ := by
  classical
  let T : GroupL2 G →L[ℂ] GroupL2 G := ∑ g ∈ A, leftRegular g
  let v := indicatorVector F
  have hpair : (inner ℂ v (T v)).re =
      ∑ g ∈ A, ((F.card : ℝ) - (translateBoundary g F).card) := by
    simp only [T, v, sum_apply, inner_sum, Complex.re_sum,
      re_inner_indicatorVector_leftRegular]
  have hlo : (A.card : ℝ) * (1 - ε) * F.card ≤ (inner ℂ v (T v)).re := by
    rw [hpair]
    calc
      _ = ∑ g ∈ A, ((1 - ε) * (F.card : ℝ)) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun g hg => by have hh := hbd g hg; nlinarith)
  have hup : (inner ℂ v (T v)).re ≤ ‖T‖ * F.card := by
    calc
      _ ≤ ‖v‖ * ‖T v‖ := re_inner_le_norm (𝕜 := ℂ) v (T v)
      _ ≤ ‖v‖ * (‖T‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm v) (norm_nonneg v)
      _ = ‖T‖ * F.card := by
        have hn : ‖v‖ ^ 2 = (F.card : ℝ) := indicatorVector_norm_sq F
        rw [← hn]
        ring
  have hpos : (0 : ℝ) < F.card := by exact_mod_cast Finset.card_pos.mpr hF
  exact le_of_mul_le_mul_right (hlo.trans hup) hpos

/-- Every finite subset of a finite-Følner subgroup has its full cardinal mass
as its actual ambient left-regular operator norm. No amenability converse is used. -/
theorem norm_sum_leftRegular_eq_card_of_finiteFoelner
    (H : Subgroup G) (hH : FiniteFoelner H) (A : Finset G)
    (hA : ∀ g ∈ A, g ∈ H) :
    ‖∑ g ∈ A, leftRegular g‖ = (A.card : ℝ) := by
  classical
  apply le_antisymm (norm_sum_leftRegular_le_card A)
  by_contra! hlt
  let N := ‖∑ g ∈ A, leftRegular g‖
  let m : ℝ := A.card
  have hm : 0 < m := lt_of_le_of_lt (norm_nonneg _) hlt
  let ε := (m - N) / (2 * m)
  have hε : 0 < ε := div_pos (sub_pos.mpr hlt) (by positivity)
  obtain ⟨F, hF, hbd⟩ := exists_ambient_foelner_set H hH A hA ε hε
  have hb := card_mul_one_sub_le_norm_sum_leftRegular_of_boundary A F hF ε hbd
  have he : ε * (2 * m) = m - N := div_mul_cancel₀ _ (ne_of_gt (by positivity : 0 < 2 * m))
  change m * (1 - ε) ≤ N at hb
  change N < m at hlt
  nlinarith

end Q1
