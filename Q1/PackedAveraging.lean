import Q1.ReducedAlgebra
import Q1.SubgroupVolume
import Q1.AveragingSimplicity

/-! Disjoint conjugate blocks give small uniform averages in the actual reduced
operator norm. All translating radii use the same ambient length. -/

noncomputable section
open scoped BigOperators
namespace Q1
variable {G : Type*} [Group G] [DecidableEq G]

/-- The conjugates of one root in a finite translating family. -/
def packedConjugateSet {N : ℕ} (t : Fin N → G) (g : G) : Finset G :=
  Finset.univ.image (fun i => t i * g * (t i)⁻¹)

theorem packedConjugates_injective {N : ℕ} (t : Fin N → G) (P : Finset G)
    (hdisj : Pairwise (fun i j => Disjoint (conjugateBlock (t i) P) (conjugateBlock (t j) P)))
    (g : G) (hg : g ∈ P) : Function.Injective (fun i => t i * g * (t i)⁻¹) := by
  intro i j hij
  change t i * g * (t i)⁻¹ = t j * g * (t j)⁻¹ at hij
  by_contra hne
  have hi : t i * g * (t i)⁻¹ ∈ conjugateBlock (t i) P := Finset.mem_image.mpr ⟨g, hg, rfl⟩
  have hj : t i * g * (t i)⁻¹ ∈ conjugateBlock (t j) P :=
    by
      rw [hij]
      exact Finset.mem_image.mpr ⟨g, hg, rfl⟩
  exact (Finset.disjoint_left.mp (hdisj hne) hi hj)

theorem card_packedConjugateSet {N : ℕ} (t : Fin N → G) (g : G)
    (hinj : Function.Injective (fun i => t i * g * (t i)⁻¹)) :
    (packedConjugateSet t g).card = N := by
  rw [packedConjugateSet, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

theorem packedConjugateSet_subset_ball (L : LengthBall G) {N : ℕ} (t : Fin N → G)
    (g : G) (R ℓ : ℕ) (ht : ∀ i, L.length (t i) ≤ R) (hg : L.length g ≤ ℓ) :
    packedConjugateSet t g ⊆ L.ball (2 * R + ℓ) := by
  intro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  apply (L.mem_ball _ _).mpr
  exact (conjugate_length_le L (t i) g).trans (by have := ht i; omega)

/-- Distinct conjugates have exactly unit indicator coefficients before averaging. -/
theorem conjugationAverage_leftRegular_eq {N : ℕ} (t : Fin N → G) (g : G)
    (hinj : Function.Injective (fun i => t i * g * (t i)⁻¹)) :
    conjugationAverage regularRepresentation t (leftRegular g) =
      (N : ℂ)⁻¹ • regularConvolution (indicatorCoefficient (packedConjugateSet t g)) := by
  rw [regularConvolution_indicator, packedConjugateSet,
    Finset.sum_image (fun i _ j _ h => hinj h)]
  simp only [conjugationAverage, regularRepresentation_apply, ← leftRegular_mul_eq_mul]

/-- The coefficient norm is sqrt(N), yielding the exact 1/sqrt(N) factor. -/
theorem norm_conjugationAverage_leftRegular_le (L : LengthBall G) {N : ℕ}
    (t : Fin N → G) (g : G) (R ℓ : ℕ)
    (ht : ∀ i, L.length (t i) ≤ R) (hg : L.length g ≤ ℓ)
    (hinj : Function.Injective (fun i => t i * g * (t i)⁻¹)) :
    ‖conjugationAverage regularRepresentation t (leftRegular g)‖ ≤
      reducedRho L (2 * R + ℓ) * Real.sqrt (1 / (N : ℝ)) := by
  rw [conjugationAverage_leftRegular_eq t g hinj, norm_smul, norm_inv, Complex.norm_natCast]
  have hbound := norm_regularConvolution_le_rho_mul (L.ball (2 * R + ℓ))
    (indicatorCoefficient (packedConjugateSet t g)) (by
      rw [support_indicatorCoefficient]
      exact packedConjugateSet_subset_ball L t g R ℓ ht hg)
  rw [coefficientL2Norm_indicator, card_packedConjugateSet t g hinj] at hbound
  calc
    (N : ℝ)⁻¹ * ‖regularConvolution (indicatorCoefficient (packedConjugateSet t g))‖ ≤
        (N : ℝ)⁻¹ * (reducedRho L (2 * R + ℓ) * Real.sqrt (N : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = reducedRho L (2 * R + ℓ) * Real.sqrt (1 / (N : ℝ)) := by
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
      have hs := Real.sqrt_div_self' (x := (N : ℝ))
      rw [div_eq_mul_inv] at hs
      calc
        _ = reducedRho L (2 * R + ℓ) * (Real.sqrt (N : ℝ) * (N : ℝ)⁻¹) := by ring
        _ = _ := by rw [hs]

/-- The same translating family controls every coefficient of a finite operator. -/
theorem norm_conjugationAverage_regularConvolution_le (L : LengthBall G) {N : ℕ}
    (t : Fin N → G) (f : G →₀ ℂ) (R ℓ : ℕ)
    (ht : ∀ i, L.length (t i) ≤ R) (hf : ∀ g ∈ f.support, L.length g ≤ ℓ)
    (hdisj : Pairwise (fun i j =>
      Disjoint (conjugateBlock (t i) f.support) (conjugateBlock (t j) f.support))) :
    ‖conjugationAverage regularRepresentation t (regularConvolution f)‖ ≤
      (∑ g ∈ f.support, ‖f g‖) *
        (reducedRho L (2 * R + ℓ) * Real.sqrt (1 / (N : ℝ))) := by
  have he : conjugationAverage regularRepresentation t (regularConvolution f) =
      ∑ g ∈ f.support, f g • conjugationAverage regularRepresentation t (leftRegular g) := by
    simp only [regularConvolution, Finsupp.sum, conjugationAverage_sum,
      conjugationAverage_smul]
  rw [he]
  calc
    ‖∑ g ∈ f.support, f g • conjugationAverage regularRepresentation t (leftRegular g)‖ ≤
        ∑ g ∈ f.support, ‖f g • conjugationAverage regularRepresentation t (leftRegular g)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ g ∈ f.support, ‖f g‖ *
        (reducedRho L (2 * R + ℓ) * Real.sqrt (1 / (N : ℝ))) := by
      apply Finset.sum_le_sum
      intro g hg
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left
        (norm_conjugationAverage_leftRegular_le L t g R ℓ ht (hf g hg)
          (packedConjugates_injective t f.support hdisj g hg)) (norm_nonneg _)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Trivial amenable radical gives logarithmic-radius disjoint conjugate blocks.
This uses only the preceding exact group-growth and packing theorems. -/
theorem logarithmic_conjugate_packing_of_trivial_radical (L : LengthBall G)
    (hR : AmenableNormalCover (⊥ : Subgroup G)) (P : Finset G) (hP : 1 ∉ P) :
    ∃ (R : ℕ → ℕ) (K B : ℝ), 0 < K ∧ 0 ≤ B ∧
      (∀ N : ℕ, 2 ≤ N → (R N : ℝ) ≤ K * Real.log (N : ℝ) + B) ∧
      ∀ N : ℕ, 2 ≤ N → ∃ t : Fin N → G,
        (∀ i, L.length (t i) ≤ R N) ∧
        Pairwise (fun i j => Disjoint (conjugateBlock (t i) P) (conjugateBlock (t j) P)) := by
  obtain ⟨c, δ, hc, hc1, hδ, hgrowth⟩ := uniform_exponential_constants P
    (fun g r => ((conjugacyBall L g r).card : ℝ)) (by
      intro g hg
      apply exponential_conjugacy_growth_of_amenableNormalCover L ⊥ hR g
      intro hb
      have he : g = 1 := Subgroup.mem_bot.mp hb
      exact hP (he ▸ hg))
  have hgr : ∀ g ∈ P, ∀ r : ℕ,
      c * Real.exp (δ * (r : ℝ)) ≤ (orbitBall (conjugationLengthBall L) r g).card := by
    intro g hg r
    rw [conjugation_orbitBall]
    have he : conjugacyBall L g r = (L.ball r).image (fun t => t * g * t⁻¹) := by
      ext y
      simp only [conjugacyBall, Finset.mem_image]
    rw [← he]
    exact hgrowth g hg r
  obtain ⟨hK, hB, hp⟩ := exponential_growth_logarithmic_packing
    (conjugationLengthBall L) P c δ hc hc1 hδ hgr
  refine ⟨exponentialPackingRadius P.card c δ, packingLogK P.card δ,
    packingLogB P.card c δ, hK, hB, fun N hN => (hp N hN).1, ?_⟩
  intro N hN
  obtain ⟨t, ht, hd⟩ := (hp N hN).2
  refine ⟨fun i => ConjAct.ofConjAct (t i), ht, ?_⟩
  exact hd

/-- Under ordinary SRD, every finite coefficient operator with zero identity
coefficient has arbitrarily small uniform conjugation averages. -/
theorem finite_zero_identity_averaging (L : LengthBall G)
    (hR : AmenableNormalCover (⊥ : Subgroup G)) (hsrd : ReducedSRD L)
    (f : G →₀ ℂ) (hf : f 1 = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ ∃ t : Fin N → G,
      ‖conjugationAverage regularRepresentation t (regularConvolution f)‖ < ε := by
  have hP : (1 : G) ∉ f.support := by simpa using hf
  obtain ⟨R, K, B, hK, _hB, hlog, hpack⟩ :=
    logarithmic_conjugate_packing_of_trivial_radical L hR f.support hP
  let ℓ := f.support.sup L.length
  have hlength : ∀ g ∈ f.support, L.length g ≤ ℓ :=
    fun g hg => Finset.le_sup (f := L.length) hg
  have htend := tendsto_srd_packing_bound (reducedRho L) (reducedRho_nonneg L)
    ((reducedSRD_iff_ordinarySRD L).mp hsrd) R K B hK ℓ 1 (by
      filter_upwards [Filter.eventually_ge_atTop 2] with N hN
      exact hlog N hN)
  have hsmall := (htend.const_mul (∑ g ∈ f.support, ‖f g‖)).eventually
    (Iio_mem_nhds (by simpa using hε))
  obtain ⟨N, hN, hs⟩ := ((Filter.eventually_ge_atTop 2).and hsmall).exists
  obtain ⟨t, ht, hd⟩ := hpack N hN
  refine ⟨N, by omega, t, ?_⟩
  exact (norm_conjugationAverage_regularConvolution_le L t f (R N) ℓ ht hlength hd).trans_lt
    (by simpa using hs)

end Q1
