import Q1.ConjugacyTuples
import Q1.ConjugacyGrowthNumeric
import Q1.FoelnerGrowth

/-! Quantitative conjugacy growth from a finite conjugate-generated subgroup
whose actual center quotient fails the finite Følner condition.
The radical and amenability permanence bridge is an explicit remaining step. -/

namespace Q1

variable {G : Type*} [Group G]

noncomputable def conjugacyBall (L : LengthBall G) (g : G) (r : ℕ) : Finset G := by
  classical
  exact (L.ball r).image (fun t => t * g * t⁻¹)

theorem conjugacyBall_mono (L : LengthBall G) (g : G) : Monotone (conjugacyBall L g) := by
  classical
  intro r s hrs
  apply Finset.image_subset_image
  intro t ht
  exact (L.mem_ball _ _).mpr (((L.mem_ball _ _).mp ht).trans hrs)

theorem conjugacyBall_nonempty (L : LengthBall G) (g : G) (r : ℕ) :
    (conjugacyBall L g r).Nonempty := by
  classical
  refine ⟨g, Finset.mem_image.mpr ⟨1, ?_, by simp⟩⟩
  exact (L.mem_ball _ _).mpr (by rw [L.length_one]; omega)

/-- The quantitative conclusion of Lemma 1 with its remaining amenability
premise stated at the actual quotient by the center. Every radius is natural,
and the ambient length is unchanged throughout the argument. -/
theorem exponential_conjugacy_growth_of_quotient_not_finiteFoelner
    (L : LengthBall G) (g : G) (A : Subgroup G) (k : ℕ) (hk : 0 < k)
    (x : Fin k → A) (u : Fin k → G)
    (hgen : Subgroup.closure (Set.range x) = ⊤)
    (hx : ∀ i, (x i : G) = u i * g * (u i)⁻¹)
    (hQ : ¬ FiniteFoelner (A ⧸ Subgroup.center A)) :
    ∃ c δ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < δ ∧
      ∀ r : ℕ, c * Real.exp (δ * r) ≤ ((conjugacyBall L g r).card : ℝ) := by
  classical
  obtain ⟨q, hq, hqgrowth⟩ := exponential_wordBall_of_not_finiteFoelner
    (quotientTupleAlphabet x) (fun s hs => quotientTupleAlphabet_inv_mem x hs)
    (quotientTupleAlphabet_generates x hgen) hQ
  let M := Finset.univ.sup (fun i : Fin k => L.length (x i : G)) + 1
  let D := Finset.univ.sup (fun i : Fin k => L.length (u i))
  have hM : 0 < M := by dsimp [M]; omega
  have hMx : ∀ i, L.length (x i : G) ≤ M := fun i =>
    (Finset.le_sup (f := fun i : Fin k => L.length (x i : G)) (Finset.mem_univ i)).trans
      (Nat.le_succ _)
  have hDu : ∀ i, L.length (u i) ≤ D := fun i =>
    Finset.le_sup (f := fun i : Fin k => L.length (u i)) (Finset.mem_univ i)
  let β : ℕ → ℝ := fun r => (conjugacyBall L g r).card
  have hβ : ∀ r, 1 ≤ β r := by
    intro r
    dsimp [β]
    exact_mod_cast (show 1 ≤ (conjugacyBall L g r).card from (conjugacyBall_nonempty L g r).card_pos)
  have hmono : Monotone β := by
    intro r s hrs
    dsimp [β]
    exact_mod_cast Finset.card_le_card (conjugacyBall_mono L g hrs)
  have hsampled : ∀ n : ℕ, q ^ n ≤ β (M * n + D) ^ k := by
    intro n
    have hc := quotient_center_wordBall_card_le_conjugacy L A x hgen g u hx M D n hMx hDu
    have hc' : ((wordBall (quotientTupleAlphabet x) n).card : ℝ) ≤ β (M * n + D) ^ k := by
      dsimp [β, conjugacyBall]
      exact_mod_cast hc
    exact (hqgrowth n).trans hc'
  exact ⟨conjugacyGrowthConstant q k M D, conjugacyGrowthRate q k M,
    conjugacyGrowthConstant_pos q k M D, conjugacyGrowthConstant_le_one q k M D hq hk hM,
    conjugacyGrowthRate_pos q k M hq hk hM,
    exponential_lower_bound_of_sampled_power β hβ hmono q k M D hq hk hM hsampled⟩

/-- Pointwise exponential growth on a finite set has uniform positive constants.
This is needed to pass from individual conjugacy roots to finite-block packing. -/
theorem uniform_exponential_constants {α : Type*} (P : Finset α) (β : α → ℕ → ℝ)
    (h : ∀ x ∈ P, ∃ c δ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < δ ∧
      ∀ r : ℕ, c * Real.exp (δ * r) ≤ β x r) :
    ∃ c δ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < δ ∧
      ∀ x ∈ P, ∀ r : ℕ, c * Real.exp (δ * r) ≤ β x r := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨1, 1, by norm_num, le_rfl, by norm_num, by simp⟩
  | @insert x P hx ih =>
    obtain ⟨c₁, δ₁, hc₁, hc₁one, hδ₁, hb₁⟩ := h x (by simp)
    obtain ⟨c₂, δ₂, hc₂, hc₂one, hδ₂, hb₂⟩ := ih (fun y hy => h y (by simp [hy]))
    refine ⟨min c₁ c₂, min δ₁ δ₂, lt_min hc₁ hc₂,
      (min_le_left _ _).trans hc₁one, lt_min hδ₁ hδ₂, ?_⟩
    intro y hy r
    rcases Finset.mem_insert.mp hy with rfl | hy
    · apply le_trans _ (hb₁ r)
      exact mul_le_mul (min_le_left _ _)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg r)))
        (Real.exp_nonneg _) hc₁.le
    · apply le_trans _ (hb₂ y hy r)
      exact mul_le_mul (min_le_right _ _)
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg r)))
        (Real.exp_nonneg _) hc₂.le

end Q1
