import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The all-natural-radius numerical extraction in written Lemma 1.
The input is a genuine sampled power lower bound, with monotone positive beta;
it is not a mere failure of subexponential growth. -/

namespace Q1

noncomputable def conjugacyGrowthRate (q : ℝ) (k M : ℕ) : ℝ :=
  Real.log q / ((k : ℝ) * M)

noncomputable def conjugacyGrowthConstant (q : ℝ) (k M D : ℕ) : ℝ :=
  Real.exp (-Real.log q / k - conjugacyGrowthRate q k M * D)

theorem conjugacyGrowthRate_pos (q : ℝ) (k M : ℕ)
    (hq : 1 < q) (hk : 0 < k) (hM : 0 < M) :
    0 < conjugacyGrowthRate q k M := by
  unfold conjugacyGrowthRate
  exact div_pos (Real.log_pos hq) (by positivity)

theorem conjugacyGrowthConstant_pos (q : ℝ) (k M D : ℕ) :
    0 < conjugacyGrowthConstant q k M D := Real.exp_pos _

theorem conjugacyGrowthConstant_le_one (q : ℝ) (k M D : ℕ)
    (hq : 1 < q) (hk : 0 < k) (hM : 0 < M) :
    conjugacyGrowthConstant q k M D ≤ 1 := by
  unfold conjugacyGrowthConstant
  apply Real.exp_le_one_iff.mpr
  have hd := conjugacyGrowthRate_pos q k M hq hk hM
  have hl := Real.log_pos hq
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : 0 ≤ Real.log q / k := div_nonneg hl.le hkr.le
  have ht : 0 ≤ conjugacyGrowthRate q k M * D := mul_nonneg hd.le (Nat.cast_nonneg D)
  rw [neg_div]
  linarith

/-- A sampled exponential bound on the kth power gives a uniform exponential
bound at every natural radius, including the finite initial segment r < D. -/
theorem exponential_lower_bound_of_sampled_power
    (β : ℕ → ℝ) (hβ : ∀ r, 1 ≤ β r) (hmono : Monotone β)
    (q : ℝ) (k M D : ℕ) (hq : 1 < q) (hk : 0 < k) (hM : 0 < M)
    (hsampled : ∀ n : ℕ, q ^ n ≤ β (M * n + D) ^ k) :
    ∀ r : ℕ, conjugacyGrowthConstant q k M D *
      Real.exp (conjugacyGrowthRate q k M * r) ≤ β r := by
  intro r
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hl : 0 < Real.log q := Real.log_pos hq
  have hd := conjugacyGrowthRate_pos q k M hq hk hM
  have hβpos : 0 < β r := lt_of_lt_of_le zero_lt_one (hβ r)
  have hlogβ : 0 ≤ Real.log (β r) := Real.log_nonneg (hβ r)
  have hexp : conjugacyGrowthConstant q k M D *
      Real.exp (conjugacyGrowthRate q k M * r) =
      Real.exp (-Real.log q / k + conjugacyGrowthRate q k M * ((r : ℝ) - D)) := by
    rw [conjugacyGrowthConstant, ← Real.exp_add]
    congr 1
    ring
  rw [hexp, ← Real.exp_log hβpos]
  apply Real.exp_le_exp.mpr
  by_cases hr : D ≤ r
  · let n := (r - D) / M
    have hnle : M * n + D ≤ r := by
      have hh := Nat.div_mul_le_self (r - D) M
      dsimp [n]
      rw [Nat.mul_comm]
      omega
    have hngt : r < M * (n + 1) + D := by
      have hh := Nat.mod_lt (r - D) hM
      have he := Nat.mod_add_div (r - D) M
      dsimp [n]
      nlinarith [Nat.sub_add_cancel hr]
    have hs : q ^ n ≤ β r ^ k :=
      (hsampled n).trans (pow_le_pow_left₀ (by linarith [hβ (M * n + D)])
        (hmono hnle) k)
    have hlogs : (n : ℝ) * Real.log q ≤ (k : ℝ) * Real.log (β r) := by
      have hh := Real.log_le_log (pow_pos hq0 n) hs
      simpa only [Real.log_pow] using hh
    have hnr : (r : ℝ) - D < (M : ℝ) * ((n : ℝ) + 1) := by
      have hh : (r : ℝ) < (M : ℝ) * ((n : ℝ) + 1) + D := by exact_mod_cast hngt
      linarith
    have hrateM : conjugacyGrowthRate q k M * (M : ℝ) = Real.log q / k := by
      unfold conjugacyGrowthRate
      field_simp
    have hlogs' : (n : ℝ) * (Real.log q / k) ≤ Real.log (β r) := by
      apply (mul_le_mul_iff_left₀ hkr).mp
      have he : ((n : ℝ) * (Real.log q / k)) * (k : ℝ) = (n : ℝ) * Real.log q := by field_simp
      rw [he]
      simpa only [mul_comm (Real.log (β r)) (k : ℝ)] using hlogs
    have hscaled : conjugacyGrowthRate q k M * ((r : ℝ) - D) <
        conjugacyGrowthRate q k M * ((M : ℝ) * ((n : ℝ) + 1)) :=
      mul_lt_mul_of_pos_left hnr hd
    rw [← mul_assoc, hrateM] at hscaled
    rw [neg_div]
    nlinarith
  · have hrle : (r : ℝ) - D ≤ 0 := by
      have hh : (r : ℝ) ≤ D := by exact_mod_cast (show r ≤ D from by omega)
      linarith
    have hh := mul_nonpos_of_nonneg_of_nonpos hd.le hrle
    have hh' := div_nonneg hl.le hkr.le
    rw [neg_div]
    linarith

end Q1
