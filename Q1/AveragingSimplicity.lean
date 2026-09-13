import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.TwoSidedIdeal.BigOperators
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.Tactic.Linarith

/-!
# Uniform conjugation averaging implies actual ideal simplicity

The averaging hypothesis quantifies over all algebra elements and every positive
norm tolerance. The functional is required to be faithful on `star a * a`.
These two hypotheses imply simplicity for all algebraic two-sided ideals;
closed-ideal simplicity is then an immediate consequence. No assumption that an
ideal is closed under `star` is used.
-/

noncomputable section

open scoped BigOperators

namespace Q1

/-- Actual closed two-sided ideal simplicity of a normed unital ring. -/
def CStarSimple (A : Type*) [NormedRing A] : Prop :=
  ∀ I : TwoSidedIdeal A, IsClosed (I : Set A) → I = ⊥ ∨ I = ⊤

variable {G A : Type*} [Group G] [CStarAlgebra A]

/-- The uniform average of the inner conjugates indexed by `t : Fin N → G`.
The definition includes `N = 0`; the averaging property requires `0 < N`. -/
def conjugationAverage (u : G →* A) {N : ℕ} (t : Fin N → G) (a : A) : A :=
  (N : ℂ)⁻¹ • ∑ i, u (t i) * a * u ((t i)⁻¹)

/-- Every algebra element admits a finite uniform conjugation average arbitrarily
close, in its actual algebra norm, to its functional value times the identity. -/
def HasConjugationAveraging (u : G →* A) (τ : A →L[ℂ] ℂ) : Prop :=
  ∀ a : A, ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, 0 < N ∧ ∃ t : Fin N → G,
      ‖conjugationAverage u t a - τ a • (1 : A)‖ < ε

/-- Uniform conjugation averaging fixes zero. -/
@[simp]
theorem conjugationAverage_zero (u : G →* A) {N : ℕ} (t : Fin N → G) :
    conjugationAverage u t (0 : A) = 0 := by
  simp only [conjugationAverage, mul_zero, zero_mul, Finset.sum_const_zero, smul_zero]

/-- Every nonempty uniform conjugation average fixes the identity. -/
theorem conjugationAverage_one (u : G →* A) {N : ℕ} (t : Fin N → G) (hN : 0 < N) :
    conjugationAverage u t (1 : A) = 1 := by
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hc : ∀ i : Fin N, u (t i) * (1 : A) * u ((t i)⁻¹) = 1 := by
    intro i
    simp only [mul_one, ← map_mul, mul_inv_cancel, map_one]
  simp only [conjugationAverage, hc, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul ℂ N (1 : A), smul_smul, inv_mul_cancel₀ hNc, one_smul]

/-- Uniform conjugation averaging preserves addition. -/
theorem conjugationAverage_add (u : G →* A) {N : ℕ} (t : Fin N → G)
    (a b : A) :
    conjugationAverage u t (a + b) =
      conjugationAverage u t a + conjugationAverage u t b := by
  simp only [conjugationAverage, mul_add, add_mul, Finset.sum_add_distrib, smul_add]

/-- Uniform conjugation averaging preserves subtraction. -/
theorem conjugationAverage_sub (u : G →* A) {N : ℕ} (t : Fin N → G)
    (a b : A) :
    conjugationAverage u t (a - b) =
      conjugationAverage u t a - conjugationAverage u t b := by
  simp only [conjugationAverage, mul_sub, sub_mul, Finset.sum_sub_distrib, smul_sub]

/-- Uniform conjugation averaging is complex linear. -/
theorem conjugationAverage_smul (u : G →* A) {N : ℕ} (t : Fin N → G)
    (c : ℂ) (a : A) :
    conjugationAverage u t (c • a) = c • conjugationAverage u t a := by
  simp only [conjugationAverage, mul_smul_comm, smul_mul_assoc, ← Finset.smul_sum]
  exact smul_comm _ _ _

/-- Uniform conjugation averaging commutes with every finite sum. -/
theorem conjugationAverage_sum (u : G →* A) {N : ℕ} (t : Fin N → G)
    {ι : Type*} (s : Finset ι) (f : ι → A) :
    conjugationAverage u t (∑ i ∈ s, f i) = ∑ i ∈ s, conjugationAverage u t (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, conjugationAverage_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi, conjugationAverage_add, ih]

/-- If the group elements have norm at most one, each inner conjugation is
contractive. -/
theorem norm_innerConjugation_le (u : G →* A) (hu : ∀ g : G, ‖u g‖ ≤ 1)
    (g : G) (a : A) : ‖u g * a * u g⁻¹‖ ≤ ‖a‖ := by
  calc
    ‖u g * a * u g⁻¹‖ ≤ ‖u g * a‖ * ‖u g⁻¹‖ := norm_mul_le _ _
    _ ≤ (1 * ‖a‖) * 1 :=
      mul_le_mul
        ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hu g) (norm_nonneg a)))
        (hu g⁻¹) (norm_nonneg _) (mul_nonneg zero_le_one (norm_nonneg a))
    _ = ‖a‖ := by rw [one_mul, mul_one]

/-- A nonempty uniform average of contractive inner conjugations is contractive
in the actual algebra norm. -/
theorem norm_conjugationAverage_le (u : G →* A) (hu : ∀ g : G, ‖u g‖ ≤ 1)
    {N : ℕ} (hN : 0 < N) (t : Fin N → G) (a : A) :
    ‖conjugationAverage u t a‖ ≤ ‖a‖ := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  have hsum : (∑ i, ‖u (t i) * a * u ((t i)⁻¹)‖) ≤ (N : ℝ) * ‖a‖ := by
    calc
      (∑ i, ‖u (t i) * a * u ((t i)⁻¹)‖) ≤ ∑ _i : Fin N, ‖a‖ :=
        Finset.sum_le_sum fun i _hi => norm_innerConjugation_le u hu (t i) a
      _ = (N : ℝ) * ‖a‖ := by simp
  calc
    ‖conjugationAverage u t a‖ =
        (N : ℝ)⁻¹ * ‖∑ i, u (t i) * a * u ((t i)⁻¹)‖ := by
      simp only [conjugationAverage, norm_smul, norm_inv, Complex.norm_natCast]
    _ ≤ (N : ℝ)⁻¹ * ((N : ℝ) * ‖a‖) :=
      mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans hsum)
        (inv_nonneg.mpr (Nat.cast_nonneg N))
    _ = ‖a‖ := by rw [← mul_assoc, inv_mul_cancel₀ hNreal, one_mul]

/-- Averaging on a dense set extends to all elements if the conjugations and
the functional are contractive. The dense approximation and the averaging
tolerance are each `ε / 3`. -/
theorem hasConjugationAveraging_of_dense [Nontrivial A]
    (u : G →* A) (τ : A →L[ℂ] ℂ)
    (hu : ∀ g : G, ‖u g‖ ≤ 1) (hτ : ∀ a : A, ‖τ a‖ ≤ ‖a‖)
    (D : Set A) (hD : Dense D)
    (haverage : ∀ a ∈ D, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, 0 < N ∧ ∃ t : Fin N → G,
        ‖conjugationAverage u t a - τ a • (1 : A)‖ < ε) :
    HasConjugationAveraging u τ := by
  intro b ε hε
  have hthird : 0 < ε / 3 := by linarith
  obtain ⟨a, ha, hab⟩ := hD.exists_dist_lt b hthird
  rw [dist_eq_norm] at hab
  obtain ⟨N, hN, t, ht⟩ := haverage a ha (ε / 3) hthird
  refine ⟨N, hN, t, ?_⟩
  have hdiff : ‖conjugationAverage u t b - conjugationAverage u t a‖ ≤ ‖b - a‖ := by
    rw [← conjugationAverage_sub]
    exact norm_conjugationAverage_le u hu hN t (b - a)
  have hscalar : ‖τ a • (1 : A) - τ b • (1 : A)‖ ≤ ‖b - a‖ := by
    rw [← sub_smul, ← map_sub, norm_smul, norm_one, mul_one]
    exact (hτ (a - b)).trans_eq (norm_sub_rev a b)
  calc
    ‖conjugationAverage u t b - τ b • (1 : A)‖ =
        ‖(conjugationAverage u t b - conjugationAverage u t a) +
          (conjugationAverage u t a - τ a • (1 : A)) +
          (τ a • (1 : A) - τ b • (1 : A))‖ := by
      congr 1
      abel
    _ ≤ ‖conjugationAverage u t b - conjugationAverage u t a‖ +
        ‖conjugationAverage u t a - τ a • (1 : A)‖ +
        ‖τ a • (1 : A) - τ b • (1 : A)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖b - a‖ + ‖conjugationAverage u t a - τ a • (1 : A)‖ + ‖b - a‖ :=
      add_le_add (add_le_add hdiff le_rfl) hscalar
    _ < ε := by linarith

/-- A two-sided ideal absorbs complex scalar multiplication because scalar
multiplication is multiplication by the image of the scalar in the algebra. -/
theorem twoSidedIdeal_complex_smul_mem (I : TwoSidedIdeal A)
    (c : ℂ) {a : A} (ha : a ∈ I) : c • a ∈ I := by
  rw [Algebra.smul_def]
  exact I.mul_mem_left _ _ ha

/-- Each uniform conjugation average remains in every two-sided ideal containing
the averaged element. Both multiplication absorption properties are used. -/
theorem conjugationAverage_mem (u : G →* A) {N : ℕ} (t : Fin N → G)
    (I : TwoSidedIdeal A) {a : A} (ha : a ∈ I) :
    conjugationAverage u t a ∈ I := by
  apply twoSidedIdeal_complex_smul_mem
  apply I.finsetSum_mem
  intro i _
  exact I.mul_mem_right _ _ (I.mul_mem_left _ _ ha)

/-- A two-sided ideal containing an invertible element is the whole ring. -/
theorem twoSidedIdeal_eq_top_of_isUnit_mem (I : TwoSidedIdeal A)
    {a : A} (ha : a ∈ I) (hu : IsUnit a) : I = ⊤ := by
  rcases hu with ⟨v, rfl⟩
  apply I.eq_top
  simpa only [Units.inv_mul] using I.mul_mem_left (↑(v⁻¹) : A) (↑v : A) ha

/-- Uniform conjugation averaging and faithfulness on positive squares imply
simplicity for actual algebraic two-sided ideals, even without ideal closedness
or closure under `star`. -/
theorem twoSidedIdeal_eq_bot_or_top_of_conjugationAveraging
    (u : G →* A) (τ : A →L[ℂ] ℂ)
    (hfaithful : ∀ a : A, a ≠ 0 → τ (star a * a) ≠ 0)
    (haverage : HasConjugationAveraging u τ) (I : TwoSidedIdeal A) :
    I = ⊥ ∨ I = ⊤ := by
  by_cases hI : I = ⊥
  · exact Or.inl hI
  right
  have hex : ∃ a : A, a ∈ I ∧ a ≠ 0 := by
    by_contra! h
    apply hI
    apply le_antisymm _ bot_le
    intro a ha
    simpa only [TwoSidedIdeal.mem_bot] using h a ha
  obtain ⟨a, ha, hane⟩ := hex
  let b : A := star a * a
  have hb : b ∈ I := I.mul_mem_left _ _ ha
  have hc : τ b ≠ 0 := hfaithful a hane
  have hcnorm : 0 < ‖τ b‖ := norm_pos_iff.mpr hc
  obtain ⟨N, _hN, t, ht⟩ := haverage b ‖τ b‖ hcnorm
  let x : A := conjugationAverage u t b
  have hx : x ∈ I := conjugationAverage_mem u t I hb
  let y : A := (τ b)⁻¹ • x
  have hy : y ∈ I := twoSidedIdeal_complex_smul_mem I _ hx
  have hdiff : y - 1 = (τ b)⁻¹ • (x - τ b • (1 : A)) := by
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ hc, one_smul, y]
  have hnorm : ‖y - 1‖ < 1 := by
    rw [hdiff, norm_smul, norm_inv]
    calc
      ‖τ b‖⁻¹ * ‖x - τ b • (1 : A)‖ < ‖τ b‖⁻¹ * ‖τ b‖ :=
        mul_lt_mul_of_pos_left ht (inv_pos.mpr hcnorm)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hcnorm)
  have hu : IsUnit y := by
    have hnorm' : ‖1 - y‖ < 1 := by rwa [norm_sub_rev]
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hnorm'
  exact twoSidedIdeal_eq_top_of_isUnit_mem I hy hu

/-- The preceding stronger algebraic simplicity theorem yields the usual
closed two-sided ideal formulation of C*-simplicity. -/
theorem cStarSimple_of_conjugationAveraging
    (u : G →* A) (τ : A →L[ℂ] ℂ)
    (hfaithful : ∀ a : A, a ≠ 0 → τ (star a * a) ≠ 0)
    (haverage : HasConjugationAveraging u τ) : CStarSimple A := by
  intro I _hclosed
  exact twoSidedIdeal_eq_bot_or_top_of_conjugationAveraging u τ hfaithful haverage I

end Q1
