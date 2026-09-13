import Q1.RegularRepresentation
import Q1.FiniteNormBounds
import Q1.WordLength
import Q1.LogSRD

/-! The reduced norm growth function is built from the actual convolution
operators on the full complex ℓ² space. Suprema include the zero coefficient,
whose ratio is zero; the nonzero version is identified on nonempty balls. -/

noncomputable section

namespace Q1

variable {G : Type*} [Group G]

/-- Actual reduced regular norm divided by the counting-measure coefficient
ℓ² norm. Division by zero assigns the zero coefficient the value zero. -/
def reducedRatio (f : G →₀ ℂ) : ℝ :=
  ‖regularConvolution f‖ / coefficientL2Norm f

/-- All reduced norm ratios with support contained in the specified finite set. -/
def reducedRatios (B : Finset G) : Set ℝ :=
  {x | ∃ f : G →₀ ℂ, f.support ⊆ B ∧ reducedRatio f = x}

/-- The actual reduced-norm growth constant on a finite support set. -/
def reducedBallRho (B : Finset G) : ℝ := sSup (reducedRatios B)

/-- The same construction on the specified ambient length balls. -/
def reducedRho (L : LengthBall G) (r : ℕ) : ℝ := reducedBallRho (L.ball r)

/-- Finite-support Cauchy--Schwarz controls the actual convolution norm. -/
theorem norm_regularConvolution_le_sqrt_card (f : G →₀ ℂ) :
    ‖regularConvolution f‖ ≤ Real.sqrt (f.support.card : ℝ) * coefficientL2Norm f := by
  have hn : 0 ≤ coefficientL2Norm f := norm_nonneg _
  calc
    ‖regularConvolution f‖ ≤ ∑ g ∈ f.support, ‖f g‖ := norm_regularConvolution_le f
    _ ≤ Real.sqrt (f.support.card : ℝ) * Real.sqrt (∑ g ∈ f.support, ‖f g‖ ^ 2) :=
      sum_norm_le_sqrt_card_mul_sqrt_sum f.support f
    _ = Real.sqrt (f.support.card : ℝ) * coefficientL2Norm f := by
      rw [← coefficientL2Norm_sq, Real.sqrt_sq hn]

/-- The ambient support set, rather than any intrinsic subgroup ball, controls
all ratios used to define rho. -/
theorem reducedRatio_le_sqrt_card (B : Finset G) (f : G →₀ ℂ) (hf : f.support ⊆ B) :
    reducedRatio f ≤ Real.sqrt (B.card : ℝ) := by
  have hcard : (f.support.card : ℝ) ≤ B.card := by exact_mod_cast Finset.card_le_card hf
  apply ratio_le_sqrt_card_of_norm_bound _ _ _ (norm_nonneg _)
  exact (norm_regularConvolution_le_sqrt_card f).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcard) (norm_nonneg _))

theorem reducedRatios_bddAbove (B : Finset G) : BddAbove (reducedRatios B) := by
  refine ⟨Real.sqrt (B.card : ℝ), ?_⟩
  rintro x ⟨f, hf, rfl⟩
  exact reducedRatio_le_sqrt_card B f hf

theorem reducedRatios_nonempty (B : Finset G) : (reducedRatios B).Nonempty :=
  ⟨reducedRatio 0, 0, by simp, rfl⟩

theorem reducedRatio_nonneg (f : G →₀ ℂ) : 0 ≤ reducedRatio f :=
  div_nonneg (norm_nonneg _) (norm_nonneg _)

theorem reducedRatio_le_rho (B : Finset G) (f : G →₀ ℂ) (hf : f.support ⊆ B) :
    reducedRatio f ≤ reducedBallRho B :=
  le_csSup (reducedRatios_bddAbove B) ⟨f, hf, rfl⟩

theorem reducedBallRho_nonneg (B : Finset G) : 0 ≤ reducedBallRho B :=
  (reducedRatio_nonneg 0).trans (reducedRatio_le_rho B 0 (by simp))

theorem reducedBallRho_le_sqrt_card (B : Finset G) :
    reducedBallRho B ≤ Real.sqrt (B.card : ℝ) := by
  apply csSup_le (reducedRatios_nonempty B)
  rintro x ⟨f, hf, rfl⟩
  exact reducedRatio_le_sqrt_card B f hf

theorem reducedBallRho_mono {A B : Finset G} (h : A ⊆ B) :
    reducedBallRho A ≤ reducedBallRho B := by
  apply csSup_le_csSup (reducedRatios_bddAbove B) (reducedRatios_nonempty A)
  rintro x ⟨f, hf, rfl⟩
  exact ⟨f, hf.trans h, rfl⟩

@[simp] theorem reducedRatio_single_one (g : G) :
    reducedRatio (Finsupp.single g (1 : ℂ)) = 1 := by
  simp [reducedRatio]

theorem one_le_reducedBallRho (B : Finset G) (hB : B.Nonempty) :
    1 ≤ reducedBallRho B := by
  obtain ⟨g, hg⟩ := hB
  have hs : (Finsupp.single g (1 : ℂ)).support ⊆ B := by simpa using hg
  simpa using reducedRatio_le_rho B (Finsupp.single g (1 : ℂ)) hs

/-- The defining reduced-norm estimate, including the zero coefficient. -/
theorem norm_regularConvolution_le_rho_mul (B : Finset G) (f : G →₀ ℂ)
    (hf : f.support ⊆ B) :
    ‖regularConvolution f‖ ≤ reducedBallRho B * coefficientL2Norm f := by
  by_cases hz : coefficientL2Norm f = 0
  · simpa [hz] using norm_regularConvolution_le_sqrt_card f
  · have hp : 0 < coefficientL2Norm f := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    exact (div_le_iff₀ hp).mp (reducedRatio_le_rho B f hf)

theorem one_le_reducedRho (L : LengthBall G) (r : ℕ) : 1 ≤ reducedRho L r := by
  apply one_le_reducedBallRho
  exact ⟨1, (L.mem_ball 1 r).mpr (by simp [L.length_one])⟩

theorem reducedRho_nonneg (L : LengthBall G) (r : ℕ) : 0 ≤ reducedRho L r :=
  zero_le_one.trans (one_le_reducedRho L r)

theorem reducedRho_le_sqrt_card (L : LengthBall G) (r : ℕ) :
    reducedRho L r ≤ Real.sqrt ((L.ball r).card : ℝ) :=
  reducedBallRho_le_sqrt_card (L.ball r)

theorem reducedRho_monotone (L : LengthBall G) : Monotone (reducedRho L) := by
  intro r s hrs
  apply reducedBallRho_mono
  intro g hg
  exact (L.mem_ball g s).mpr (((L.mem_ball g r).mp hg).trans hrs)

/-- Polynomial rapid decay for the actual reduced-norm growth function. -/
def ReducedRD (L : LengthBall G) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ d : ℝ, 0 ≤ d ∧
    ∀ r : ℕ, reducedRho L r ≤ C * (1 + (r : ℝ)) ^ d

/-- Ordinary sub-rapid decay for the actual reduced-norm growth function. -/
def ReducedSRD (L : LengthBall G) : Prop :=
  Filter.Tendsto (fun n : ℕ => Real.log (reducedRho L n) / (n : ℝ))
    Filter.atTop (nhds 0)

theorem reducedSRD_iff_ordinarySRD (L : LengthBall G) :
    ReducedSRD L ↔ OrdinarySRD (reducedRho L) :=
  (ordinarySRD_iff_log_limit (reducedRho L) (one_le_reducedRho L)).symm

theorem ReducedRD.subrapid {L : LengthBall G} (h : ReducedRD L) : ReducedSRD L := by
  obtain ⟨C, _, d, _, hbound⟩ := h
  exact (reducedSRD_iff_ordinarySRD L).mpr
    (ordinarySRD_of_polynomial_bound (reducedRho L) C d hbound)

/-- The original nonzero-coefficient ratio set. -/
def nonzeroReducedRatios (B : Finset G) : Set ℝ :=
  {x | ∃ f : G →₀ ℂ, f ≠ 0 ∧ f.support ⊆ B ∧ reducedRatio f = x}

theorem nonzeroReducedRatios_subset (B : Finset G) :
    nonzeroReducedRatios B ⊆ reducedRatios B := by
  rintro x ⟨f, _, hf, rfl⟩
  exact ⟨f, hf, rfl⟩

theorem nonzeroReducedRatios_bddAbove (B : Finset G) :
    BddAbove (nonzeroReducedRatios B) :=
  (reducedRatios_bddAbove B).mono (nonzeroReducedRatios_subset B)

theorem one_mem_nonzeroReducedRatios (B : Finset G) (hB : B.Nonempty) :
    1 ∈ nonzeroReducedRatios B := by
  obtain ⟨g, hg⟩ := hB
  refine ⟨Finsupp.single g 1, by simp, by simpa using hg, reducedRatio_single_one g⟩

/-- Including the zero coefficient does not change the exact original
nonzero-coefficient supremum on any nonempty ball. -/
theorem reducedBallRho_eq_sSup_nonzero (B : Finset G) (hB : B.Nonempty) :
    reducedBallRho B = sSup (nonzeroReducedRatios B) := by
  have hb := nonzeroReducedRatios_bddAbove B
  have h1 : 1 ≤ sSup (nonzeroReducedRatios B) :=
    le_csSup hb (one_mem_nonzeroReducedRatios B hB)
  apply le_antisymm
  · apply csSup_le (reducedRatios_nonempty B)
    rintro x ⟨f, hf, rfl⟩
    by_cases hz : f = 0
    · simpa [hz, reducedRatio] using zero_le_one.trans h1
    · exact le_csSup hb ⟨f, hz, hf, rfl⟩
  · exact csSup_le_csSup (reducedRatios_bddAbove B)
      ⟨1, one_mem_nonzeroReducedRatios B hB⟩ (nonzeroReducedRatios_subset B)

end Q1
