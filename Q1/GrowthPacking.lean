import Q1.Displacement
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Exponential rooted growth gives logarithmic-radius packing

The exponential orbit-growth bound and `LengthBall` remain explicit inputs.
No threshold-existence, packing, amenability, or analytic norm axiom is assumed.
-/

namespace Q1

/-- A positive polynomial envelope for the largest finite packing threshold. -/
def packingEnvelope (m : ℕ) : ℕ := m * (m.factorial * m ^ m) + 1

/-- The real input to the natural ceiling defining the displacement radius. -/
noncomputable def packingLogInput (m : ℕ) (c δ : ℝ) (N : ℕ) : ℝ :=
  (Real.log ((packingEnvelope m : ℝ) / c) + (m : ℝ) * Real.log (N : ℝ)) / δ

/-- An explicit natural radius sufficient for the finite orbit threshold. -/
noncomputable def exponentialPackingA (m : ℕ) (c δ : ℝ) (N : ℕ) : ℕ :=
  Nat.ceil (packingLogInput m c δ N)

/-- The common natural radius of all the disjoint packed blocks. -/
noncomputable def exponentialPackingRadius (m : ℕ) (c δ : ℝ) (N : ℕ) : ℕ :=
  (2 ^ m - 1) * exponentialPackingA m c δ N

/-- A strictly positive logarithmic coefficient; the extra one is harmless. -/
noncomputable def packingLogK (m : ℕ) (δ : ℝ) : ℝ :=
  ((2 ^ m - 1 : ℕ) : ℝ) * (m : ℝ) / δ + 1

noncomputable def packingLogB (m : ℕ) (c δ : ℝ) : ℝ :=
  ((2 ^ m - 1 : ℕ) : ℝ) *
    (Real.log ((packingEnvelope m : ℝ) / c) / δ + 1)

theorem packingEnvelope_pos (m : ℕ) : 0 < packingEnvelope m := by
  unfold packingEnvelope
  omega

theorem packing_threshold_le_envelope (m N : ℕ) :
    m * (m.factorial * ((N - 1) * m) ^ m) ≤
      (packingEnvelope m - 1) * N ^ m := by
  calc
    m * (m.factorial * ((N - 1) * m) ^ m) ≤
        m * (m.factorial * (N * m) ^ m) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_left (Nat.mul_le_mul_right m (Nat.sub_le N 1)) m))
    _ = (packingEnvelope m - 1) * N ^ m := by
      simp only [packingEnvelope, Nat.add_sub_cancel, mul_pow]
      ring

theorem packing_threshold_lt_envelope (m N : ℕ) (hN : 1 ≤ N) :
    m * (m.factorial * ((N - 1) * m) ^ m) < packingEnvelope m * N ^ m := by
  apply lt_of_le_of_lt (packing_threshold_le_envelope m N)
  exact Nat.mul_lt_mul_of_pos_right
    (Nat.sub_lt (packingEnvelope_pos m) (by decide)) (pow_pos (by omega) m)

/-- The exponential lower bound at the ceiling radius strictly exceeds the threshold. -/
theorem packing_threshold_lt_exp (m N : ℕ) (c δ : ℝ)
    (hc : 0 < c) (hδ : 0 < δ) (hN : 1 ≤ N) :
    (m * (m.factorial * ((N - 1) * m) ^ m) : ℕ) <
      c * Real.exp (δ * (exponentialPackingA m c δ N : ℝ)) := by
  have hC : 0 < (packingEnvelope m : ℝ) := by exact_mod_cast packingEnvelope_pos m
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hceil := Nat.le_ceil (packingLogInput m c δ N)
  have hscaled :
      Real.log ((packingEnvelope m : ℝ) / c) + (m : ℝ) * Real.log (N : ℝ) ≤
        δ * (exponentialPackingA m c δ N : ℝ) := by
    have hh := (div_le_iff₀ hδ).mp hceil
    simpa only [packingLogInput, exponentialPackingA, mul_comm] using hh
  calc
    ((m * (m.factorial * ((N - 1) * m) ^ m) : ℕ) : ℝ) <
        (packingEnvelope m : ℝ) * (N : ℝ) ^ m := by
      exact_mod_cast packing_threshold_lt_envelope m N hN
    _ = c * Real.exp
        (Real.log ((packingEnvelope m : ℝ) / c) + (m : ℝ) * Real.log (N : ℝ)) := by
      rw [Real.exp_add, Real.exp_log (div_pos hC hc), Real.exp_nat_mul,
        Real.exp_log hNr]
      field_simp
    _ ≤ c * Real.exp (δ * (exponentialPackingA m c δ N : ℝ)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hscaled) hc.le

theorem packingLogInput_nonneg (m N : ℕ) (c δ : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ) (hN : 1 ≤ N) :
    0 ≤ packingLogInput m c δ N := by
  have hC : (1 : ℝ) ≤ (packingEnvelope m : ℝ) := by
    exact_mod_cast (show 1 ≤ packingEnvelope m from packingEnvelope_pos m)
  have hratio : 1 ≤ (packingEnvelope m : ℝ) / c := by
    apply (le_div_iff₀ hc).mpr
    simpa using hc1.trans hC
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  unfold packingLogInput
  exact div_nonneg
    (add_nonneg (Real.log_nonneg hratio)
      (mul_nonneg (Nat.cast_nonneg m) (Real.log_nonneg hNr))) hδ.le

theorem packingLogK_pos (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    0 < packingLogK m δ := by
  unfold packingLogK
  positivity

theorem packingLogB_nonneg (m : ℕ) (c δ : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ) :
    0 ≤ packingLogB m c δ := by
  have hC : (1 : ℝ) ≤ (packingEnvelope m : ℝ) := by
    exact_mod_cast (show 1 ≤ packingEnvelope m from packingEnvelope_pos m)
  have hratio : 1 ≤ (packingEnvelope m : ℝ) / c := by
    apply (le_div_iff₀ hc).mpr
    simpa using hc1.trans hC
  unfold packingLogB
  exact mul_nonneg (Nat.cast_nonneg _)
    (add_nonneg (div_nonneg (Real.log_nonneg hratio) hδ.le) zero_le_one)

/-- The explicit natural packing radius has the required logarithmic bound. -/
theorem exponentialPackingRadius_le_log (m N : ℕ) (c δ : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ) (hN : 1 ≤ N) :
    (exponentialPackingRadius m c δ N : ℝ) ≤
      packingLogK m δ * Real.log (N : ℝ) + packingLogB m c δ := by
  have hA : (exponentialPackingA m c δ N : ℝ) ≤ packingLogInput m c δ N + 1 :=
    (Nat.ceil_lt_add_one (packingLogInput_nonneg m N c δ hc hc1 hδ hN)).le
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hN)
  calc
    (exponentialPackingRadius m c δ N : ℝ) =
        ((2 ^ m - 1 : ℕ) : ℝ) * (exponentialPackingA m c δ N : ℝ) := by
      simp only [exponentialPackingRadius, Nat.cast_mul]
    _ ≤ ((2 ^ m - 1 : ℕ) : ℝ) * (packingLogInput m c δ N + 1) :=
      mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _)
    _ = (((2 ^ m - 1 : ℕ) : ℝ) * (m : ℝ) / δ) * Real.log (N : ℝ) +
        packingLogB m c δ := by
      unfold packingLogInput packingLogB
      ring
    _ ≤ packingLogK m δ * Real.log (N : ℝ) + packingLogB m c δ := by
      unfold packingLogK
      nlinarith

variable {G α : Type*} [Group G] [MulAction G α] [DecidableEq α]

/-- Exponential rooted orbit growth supplies all finite thresholds needed for packing. -/
theorem exponential_growth_packing (L : LengthBall G) (P : Finset α)
    (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hgrowth : ∀ x ∈ P, ∀ r : ℕ,
      c * Real.exp (δ * (r : ℝ)) ≤ (orbitBall L r x).card)
    (N : ℕ) (hN : 1 ≤ N) :
    ∃ t : Fin N → G,
      (∀ i, L.length (t i) ≤ exponentialPackingRadius P.card c δ N) ∧
      Pairwise (fun i j => Disjoint (imageBlock (t i) P) (imageBlock (t j) P)) := by
  apply finite_threshold_packing L P N (exponentialPackingA P.card c δ N)
  intro x hx
  have h := lt_of_lt_of_le (packing_threshold_lt_exp P.card N c δ hc hδ hN)
    (hgrowth x hx (exponentialPackingA P.card c δ N))
  exact_mod_cast h

/-- A packaged explicit-radius result, suitable for the later analytic interface. -/
theorem exponential_growth_logarithmic_packing (L : LengthBall G) (P : Finset α)
    (c δ : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ)
    (hgrowth : ∀ x ∈ P, ∀ r : ℕ,
      c * Real.exp (δ * (r : ℝ)) ≤ (orbitBall L r x).card) :
    0 < packingLogK P.card δ ∧ 0 ≤ packingLogB P.card c δ ∧
      ∀ N : ℕ, 2 ≤ N →
        (exponentialPackingRadius P.card c δ N : ℝ) ≤
          packingLogK P.card δ * Real.log (N : ℝ) + packingLogB P.card c δ ∧
        ∃ t : Fin N → G,
          (∀ i, L.length (t i) ≤ exponentialPackingRadius P.card c δ N) ∧
          Pairwise (fun i j =>
            Disjoint (imageBlock (t i) P) (imageBlock (t j) P)) := by
  refine ⟨packingLogK_pos P.card δ hδ, packingLogB_nonneg P.card c δ hc hc1 hδ, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by omega
  exact ⟨exponentialPackingRadius_le_log P.card N c δ hc hc1 hδ hN1,
    exponential_growth_packing L P c δ hc hδ hgrowth N hN1⟩

end Q1
