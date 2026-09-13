import Q1.Asymptotic

/-! Exact equivalence between the ordinary logarithmic limit and the eventual
exponential upper bound, with the required lower bound on rho explicit. -/

open Filter
open scoped Topology

namespace Q1

/-- With rho at least one, the eventual upper-exponential definition is exactly
ordinary convergence of log(rho(n))/n to zero. The term at n=0 is harmless. -/
theorem ordinarySRD_iff_log_limit (ρ : ℕ → ℝ) (hρ : ∀ n, 1 ≤ ρ n) :
    OrdinarySRD ρ ↔ Tendsto (fun n : ℕ => Real.log (ρ n) / (n : ℝ)) atTop (𝓝 0) := by
  constructor
  · intro h
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun n => lt_of_lt_of_le ha
        (div_nonneg (Real.log_nonneg (hρ n)) (Nat.cast_nonneg n))
    · intro b hb
      filter_upwards [h (b / 2) (by linarith), eventually_gt_atTop (0 : ℕ)] with n hn hn0
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
      have hp : 0 < ρ n := lt_of_lt_of_le zero_lt_one (hρ n)
      have hl : Real.log (ρ n) ≤ (b / 2) * n := by
        simpa using Real.log_le_log hp hn
      have hd := (div_le_iff₀ hnpos).mpr hl
      exact lt_of_le_of_lt hd (by linarith)
  · intro h ε hε
    filter_upwards [h.eventually (Iio_mem_nhds hε),
      eventually_gt_atTop (0 : ℕ)] with n hn hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hl : Real.log (ρ n) < ε * n := (div_lt_iff₀ hnpos).mp hn
    have hp : 0 < ρ n := lt_of_lt_of_le zero_lt_one (hρ n)
    calc
      ρ n = Real.exp (Real.log (ρ n)) := (Real.exp_log hp).symm
      _ ≤ Real.exp (ε * n) := (Real.exp_lt_exp.mpr hl).le

/-- The polynomial RD hypothesis gives the exact ordinary logarithmic SRD
limit when the growth function is at least one. -/
theorem log_limit_of_polynomial_bound (ρ : ℕ → ℝ) (hρ : ∀ n, 1 ≤ ρ n)
    (C d : ℝ) (hbound : ∀ n : ℕ, ρ n ≤ C * (1 + (n : ℝ)) ^ d) :
    Tendsto (fun n : ℕ => Real.log (ρ n) / (n : ℝ)) atTop (𝓝 0) :=
  (ordinarySRD_iff_log_limit ρ hρ).mp (ordinarySRD_of_polynomial_bound ρ C d hbound)

end Q1
