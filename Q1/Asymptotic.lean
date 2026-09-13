import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-!
# The numerical SRD contradiction at logarithmic radii

This file formalizes only the final real-variable estimate in the frozen
sunflower candidate. It assumes the numerical radius estimate explicitly;
it does not define or assert amenability, a URS, or C*-simplicity.
-/

open Filter
open scoped Topology

namespace Q1

/-- Ordinary subexponential upper growth, in the eventual exponential form. -/
def OrdinarySRD (ρ : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ρ n ≤ Real.exp (ε * (n : ℝ))

/-- Finitely many exceptional initial radii can be absorbed into a positive
multiplicative constant. No monotonicity or sign assumption on `ρ` is needed. -/
theorem OrdinarySRD.exists_global_exp_bound {ρ : ℕ → ℝ}
    (hsrd : OrdinarySRD ρ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ρ n ≤ C * Real.exp (ε * (n : ℝ)) := by
  obtain ⟨R, hR⟩ := eventually_atTop.1 (hsrd ε hε)
  let C : ℝ := max 1 (∑ i ∈ Finset.range R, |ρ i|)
  have hC : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨C, hCpos, fun n => ?_⟩
  have he : 1 ≤ Real.exp (ε * (n : ℝ)) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hε.le (Nat.cast_nonneg _))
  by_cases hn : R ≤ n
  · exact (hR n hn).trans (by
      simpa using mul_le_mul_of_nonneg_right hC (Real.exp_nonneg (ε * (n : ℝ))))
  · have hmem : n ∈ Finset.range R := Finset.mem_range.mpr (lt_of_not_ge hn)
    calc
      ρ n ≤ |ρ n| := le_abs_self _
      _ ≤ ∑ i ∈ Finset.range R, |ρ i| :=
        Finset.single_le_sum (fun i _ => abs_nonneg (ρ i)) hmem
      _ ≤ C := le_max_right _ _
      _ ≤ C * Real.exp (ε * (n : ℝ)) := by
        simpa using mul_le_mul_of_nonneg_left he hCpos.le

/-- SRD evaluated at radii tending to infinity and bounded by a logarithm,
multiplied by the square-root coefficient estimate, tends to zero. -/
theorem tendsto_srd_log_radius
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 ≤ ρ n) (hsrd : OrdinarySRD ρ)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (K B m : ℝ) (hK : 0 < K) (hm : 0 ≤ m)
    (hlog : ∀ᶠ N in atTop, (r N : ℝ) ≤ K * Real.log (N : ℝ) + B) :
    Tendsto (fun N => ρ (r N) * Real.sqrt (m / (N : ℝ))) atTop (𝓝 0) := by
  let ε : ℝ := 1 / (4 * K)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεK : ε * K = 1 / 4 := by
    dsimp [ε]
    field_simp
  have hsrd_r : ∀ᶠ N in atTop,
      ρ (r N) ≤ Real.exp (ε * (r N : ℝ)) :=
    hr.eventually (hsrd ε hε)
  have hlog_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexponent : Tendsto
      (fun N : ℕ => ε * B - Real.log (N : ℝ) / 4) atTop atBot := by
    apply tendsto_atBot.2
    intro b
    filter_upwards [hlog_top.eventually (eventually_ge_atTop (4 * (ε * B - b)))]
      with N hN
    linarith
  have hmajorant : Tendsto
      (fun N : ℕ => Real.sqrt m * Real.exp (ε * B - Real.log (N : ℝ) / 4))
      atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hexponent).const_mul (Real.sqrt m)
  apply squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (hρ (r N)) (Real.sqrt_nonneg _)) _ hmajorant
  filter_upwards [hsrd_r, hlog, eventually_gt_atTop (0 : ℕ)] with N hρN hrN hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : ℝ) = Real.exp (Real.log (N : ℝ) / 2) := by
    rw [Real.exp_half, Real.exp_log hNreal]
  have he : ε * (r N : ℝ) - Real.log (N : ℝ) / 2 ≤
      ε * B - Real.log (N : ℝ) / 4 := by
    calc
      ε * (r N : ℝ) - Real.log (N : ℝ) / 2 ≤
          ε * (K * Real.log (N : ℝ) + B) - Real.log (N : ℝ) / 2 :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hrN hε.le) _
      _ = ε * B - Real.log (N : ℝ) / 4 := by
        rw [mul_add, ← mul_assoc, hεK]
        ring
  calc
    ρ (r N) * Real.sqrt (m / (N : ℝ)) ≤
        Real.exp (ε * (r N : ℝ)) * Real.sqrt (m / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hρN (Real.sqrt_nonneg _)
    _ = Real.sqrt m * Real.exp
        (ε * (r N : ℝ) - Real.log (N : ℝ) / 2) := by
      rw [Real.sqrt_div hm, hsqrt, Real.exp_sub]
      ring
    _ ≤ Real.sqrt m * Real.exp (ε * B - Real.log (N : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Real.sqrt_nonneg _)

/-- The strict numerical inequality needed to contradict a norm lower bound of one. -/
theorem eventually_srd_log_radius_lt_one
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 ≤ ρ n) (hsrd : OrdinarySRD ρ)
    (r : ℕ → ℕ) (hr : Tendsto r atTop atTop)
    (K B m : ℝ) (hK : 0 < K) (hm : 0 ≤ m)
    (hlog : ∀ᶠ N in atTop, (r N : ℝ) ≤ K * Real.log (N : ℝ) + B) :
    ∀ᶠ N in atTop, ρ (r N) * Real.sqrt (m / (N : ℝ)) < 1 := by
  exact (tendsto_srd_log_radius ρ hρ hsrd r hr K B m hK hm hlog).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))

/-- Stronger numerical form: logarithmically bounded radii need not themselves
tend to infinity, since ordinary SRD controls the finite initial radii too. -/
theorem tendsto_srd_log_radius_without_divergence
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 ≤ ρ n) (hsrd : OrdinarySRD ρ)
    (r : ℕ → ℕ) (K B m : ℝ) (hK : 0 < K) (hm : 0 ≤ m)
    (hlog : ∀ᶠ N in atTop, (r N : ℝ) ≤ K * Real.log (N : ℝ) + B) :
    Tendsto (fun N => ρ (r N) * Real.sqrt (m / (N : ℝ))) atTop (𝓝 0) := by
  let ε : ℝ := 1 / (4 * K)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεK : ε * K = 1 / 4 := by dsimp [ε]; field_simp
  obtain ⟨C, hC, hbound⟩ := hsrd.exists_global_exp_bound hε
  have hlog_top : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexponent : Tendsto
      (fun N : ℕ => ε * B - Real.log (N : ℝ) / 4) atTop atBot := by
    apply tendsto_atBot.2
    intro b
    filter_upwards [hlog_top.eventually (eventually_ge_atTop (4 * (ε * B - b)))]
      with N hN
    linarith
  have hmajorant : Tendsto
      (fun N : ℕ => (C * Real.sqrt m) *
        Real.exp (ε * B - Real.log (N : ℝ) / 4)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp hexponent).const_mul (C * Real.sqrt m)
  apply squeeze_zero' (Eventually.of_forall fun N =>
    mul_nonneg (hρ (r N)) (Real.sqrt_nonneg _)) _ hmajorant
  filter_upwards [hlog, eventually_gt_atTop (0 : ℕ)] with N hrN hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : ℝ) = Real.exp (Real.log (N : ℝ) / 2) := by
    rw [Real.exp_half, Real.exp_log hNreal]
  have he : ε * (r N : ℝ) - Real.log (N : ℝ) / 2 ≤
      ε * B - Real.log (N : ℝ) / 4 := by
    calc
      ε * (r N : ℝ) - Real.log (N : ℝ) / 2 ≤
          ε * (K * Real.log (N : ℝ) + B) - Real.log (N : ℝ) / 2 :=
        sub_le_sub_right (mul_le_mul_of_nonneg_left hrN hε.le) _
      _ = ε * B - Real.log (N : ℝ) / 4 := by
        rw [mul_add, ← mul_assoc, hεK]
        ring
  calc
    ρ (r N) * Real.sqrt (m / (N : ℝ)) ≤
        (C * Real.exp (ε * (r N : ℝ))) * Real.sqrt (m / (N : ℝ)) :=
      mul_le_mul_of_nonneg_right (hbound (r N)) (Real.sqrt_nonneg _)
    _ = (C * Real.sqrt m) * Real.exp
        (ε * (r N : ℝ) - Real.log (N : ℝ) / 2) := by
      rw [Real.sqrt_div hm, hsqrt, Real.exp_sub]
      ring
    _ ≤ (C * Real.sqrt m) * Real.exp (ε * B - Real.log (N : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he)
        (mul_nonneg hC.le (Real.sqrt_nonneg _))

/-- Contradiction-ready form, without a divergence hypothesis on the radii. -/
theorem eventually_srd_log_radius_lt_one_without_divergence
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 ≤ ρ n) (hsrd : OrdinarySRD ρ)
    (r : ℕ → ℕ) (K B m : ℝ) (hK : 0 < K) (hm : 0 ≤ m)
    (hlog : ∀ᶠ N in atTop, (r N : ℝ) ≤ K * Real.log (N : ℝ) + B) :
    ∀ᶠ N in atTop, ρ (r N) * Real.sqrt (m / (N : ℝ)) < 1 := by
  exact (tendsto_srd_log_radius_without_divergence ρ hρ hsrd r K B m hK hm hlog).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))

/-- The exact coefficient/radius expression in the packing argument. -/
theorem tendsto_srd_packing_bound
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 ≤ ρ n) (hsrd : OrdinarySRD ρ)
    (R : ℕ → ℕ) (K B : ℝ) (hK : 0 < K) (L m : ℕ)
    (hlog : ∀ᶠ N in atTop, (R N : ℝ) ≤ K * Real.log (N : ℝ) + B) :
    Tendsto (fun N => ρ (2 * R N + L) * Real.sqrt ((m : ℝ) / (N : ℝ)))
      atTop (𝓝 0) := by
  apply tendsto_srd_log_radius_without_divergence ρ hρ hsrd
    (fun N => 2 * R N + L) (2 * K) (2 * B + (L : ℝ)) (m : ℝ)
    (by positivity) (by positivity)
  filter_upwards [hlog] with N hN
  push_cast
  linarith

/-- Numerical contradiction between the SRD packing estimate and an eventual
lower bound of one. The lower bound is an explicit assumption, not an assertion
about an unformalized operator algebra. -/
theorem false_of_srd_packing_lower_bound
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 ≤ ρ n) (hsrd : OrdinarySRD ρ)
    (R : ℕ → ℕ) (K B : ℝ) (hK : 0 < K) (L m : ℕ)
    (hlog : ∀ᶠ N in atTop, (R N : ℝ) ≤ K * Real.log (N : ℝ) + B)
    (hlower : ∀ᶠ N in atTop,
      1 ≤ ρ (2 * R N + L) * Real.sqrt ((m : ℝ) / (N : ℝ))) : False := by
  have hupper := (tendsto_srd_packing_bound ρ hρ hsrd R K B hK L m hlog).eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨N, hN⟩ := (hlower.and hupper).exists
  exact (not_lt_of_ge hN.1) hN.2

/-- A polynomial upper bound implies ordinary SRD. This even permits arbitrary
real coefficients and exponents; the usual RD assumptions `0 < C` and `0 ≤ d`
are therefore more than sufficient. -/
theorem ordinarySRD_of_polynomial_bound
    (ρ : ℕ → ℝ) (C d : ℝ)
    (hbound : ∀ n : ℕ, ρ n ≤ C * (1 + (n : ℝ)) ^ d) :
    OrdinarySRD ρ := by
  intro ε hε
  have hx : Tendsto (fun n : ℕ => 1 + (n : ℝ)) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [tendsto_natCast_atTop_atTop.eventually
      (eventually_ge_atTop (b - 1 : ℝ))] with n hn
    linarith
  have hlim : Tendsto
      (fun n : ℕ => C * Real.exp ε *
        ((1 + (n : ℝ)) ^ d * Real.exp (-ε * (1 + (n : ℝ)))))
      atTop (𝓝 0) := by
    simpa using
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero d ε hε).comp hx).const_mul
        (C * Real.exp ε)
  filter_upwards [hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hn
  have he : Real.exp ε * Real.exp (-ε * (1 + (n : ℝ))) *
      Real.exp (ε * (n : ℝ)) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    have hz : ε + -ε * (1 + (n : ℝ)) + ε * (n : ℝ) = 0 := by ring
    rw [hz, Real.exp_zero]
  have hmul := mul_lt_mul_of_pos_right hn (Real.exp_pos (ε * (n : ℝ)))
  have hid : (C * Real.exp ε *
      ((1 + (n : ℝ)) ^ d * Real.exp (-ε * (1 + (n : ℝ))))) *
      Real.exp (ε * (n : ℝ)) = C * (1 + (n : ℝ)) ^ d := by
    calc
      _ = (C * (1 + (n : ℝ)) ^ d) *
          (Real.exp ε * Real.exp (-ε * (1 + (n : ℝ))) *
            Real.exp (ε * (n : ℝ))) := by ring
      _ = _ := by rw [he, mul_one]
  rw [hid, one_mul] at hmul
  exact (hbound n).trans hmul.le

end Q1
