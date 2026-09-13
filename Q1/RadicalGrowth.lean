import Q1.RadicalCover
import Q1.FoelnerExtension
import Q1.FoelnerCommutative
import Q1.ConjugacyPackingObstruction

/-! The complete radical-to-exponential-conjugacy-growth argument of written
Lemma 1, using explicit invariant probabilities on all subsets as the
amenability convention. Its application to confinement still requires the
subgroup-volume bound; no reduced C*-algebra or URS theorem is asserted here. -/

namespace Q1

variable {G : Type*} [Group G]

/-- The center is Følner, so a Følner center quotient makes the full group Følner. -/
theorem finiteFoelner_of_center_quotient (h : FiniteFoelner (G ⧸ Subgroup.center G)) :
    FiniteFoelner G :=
  finiteFoelner_extension (Subgroup.center G) (finiteFoelner_center G) h

/-- A non-Følner normal closure provides an actual finite conjugate tuple
whose center quotient is non-Følner. -/
theorem quotient_witness_of_not_finiteFoelner_normalClosure (g : G)
    (hnot : ¬ FiniteFoelner (Subgroup.normalClosure ({g} : Set G))) :
    NonFoelnerCenterQuotientWitness g := by
  obtain ⟨A, k, hk, x, u, hgen, hx, hA⟩ := exists_conjugate_tuple_not_finiteFoelner g hnot
  refine ⟨A, k, hk, x, u, hgen, hx, ?_⟩
  exact fun hQ => hA (finiteFoelner_of_center_quotient hQ)

/-- The exact normal-amenability domination property is sufficient for the
algebraic witness; neither amenability nor normality of R itself is needed. -/
theorem quotient_witness_of_amenableNormalCover (R : Subgroup G)
    (hR : AmenableNormalCover R) (g : G) (hg : g ∉ R) :
    NonFoelnerCenterQuotientWitness g :=
  quotient_witness_of_not_finiteFoelner_normalClosure g
    (not_finiteFoelner_normalClosure_of_amenableNormalCover R hR g hg)

/-- Every element outside a normal-amenability cover has a uniform exponential
rooted conjugacy-volume lower bound, at all natural radii in the same length. -/
theorem exponential_conjugacy_growth_of_amenableNormalCover
    (L : LengthBall G) (R : Subgroup G) (hR : AmenableNormalCover R)
    (g : G) (hg : g ∉ R) :
    ∃ c δ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < δ ∧
      ∀ r : ℕ, c * Real.exp (δ * r) ≤ ((conjugacyBall L g r).card : ℝ) :=
  exponential_conjugacy_growth_of_witness L g
    (quotient_witness_of_amenableNormalCover R hR g hg)

/-- Written Lemma 1 for a supplied amenable radical with its full defining
properties. The mean is a finitely additive probability on all subsets. -/
theorem exponential_conjugacy_growth_outside_radical
    (L : LengthBall G) (R : Subgroup G) (hR : IsAmenableRadical R)
    (g : G) (hg : g ∉ R) :
    ∃ c δ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < δ ∧
      ∀ r : ℕ, c * Real.exp (δ * r) ≤ ((conjugacyBall L g r).card : ℝ) :=
  exponential_conjugacy_growth_of_amenableNormalCover L R hR.maximal g hg

/-- The concrete finite symmetric generating-set version, with the exact
shortest-word length constructed in the preceding batch. -/
theorem exponential_conjugacy_growth_wordLength
    (S : Finset G) (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤)
    (R : Subgroup G) (hR : IsAmenableRadical R) (g : G) (hg : g ∉ R) :
    ∃ c δ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < δ ∧ ∀ r : ℕ,
      c * Real.exp (δ * r) ≤
        ((conjugacyBall (wordLengthBall S hsym hgen) g r).card : ℝ) :=
  exponential_conjugacy_growth_outside_radical (wordLengthBall S hsym hgen) R hR g hg

/-- At the trivial subgroup the radical structure requires exactly normal
amenability domination: its other two defining properties are proved here. -/
theorem isAmenableRadical_bot_iff :
    IsAmenableRadical (⊥ : Subgroup G) ↔ AmenableNormalCover (⊥ : Subgroup G) := by
  constructor
  · exact fun h => h.maximal
  · intro h
    exact ⟨inferInstance, hasInvariantMean_of_finiteFoelner finiteFoelner_of_finite, h⟩

/-- Ordinary SRD obstruction after removing the prior exponential-growth input.
The witness excludes identity explicitly. The finite confinement and subgroup
volume bound remain inputs; this is not a C*-simplicity theorem. -/
theorem no_confined_subgroup_of_trivial_radical_srd_volume [DecidableEq G]
    (L : LengthBall G) (hR : AmenableNormalCover (⊥ : Subgroup G))
    (H : Subgroup G) (P : Finset G) (hP : 1 ∉ P) (hconf : ConfinedBy H P)
    (ρ : ℕ → ℝ) (hρ : ∀ r, 0 ≤ ρ r) (hsrd : OrdinarySRD ρ)
    (hvolume : ∀ r, ((subgroupBall L H r).card : ℝ) ≤ (ρ r) ^ 2) : False := by
  apply no_confined_subgroup_of_quotient_witnesses_and_srd_volume
    L H P hconf _ ρ hρ hsrd hvolume
  intro g hg
  apply quotient_witness_of_amenableNormalCover (⊥ : Subgroup G) hR g
  intro hbot
  have he : g = 1 := Subgroup.mem_bot.mp hbot
  exact hP (he ▸ hg)

/-- The polynomial-RD version is a separate corollary, obtained via the proved
polynomial-bound-to-ordinary-SRD implication. -/
theorem no_confined_subgroup_of_trivial_radical_rd_volume [DecidableEq G]
    (L : LengthBall G) (hR : AmenableNormalCover (⊥ : Subgroup G))
    (H : Subgroup G) (P : Finset G) (hP : 1 ∉ P) (hconf : ConfinedBy H P)
    (ρ : ℕ → ℝ) (hρ : ∀ r, 0 ≤ ρ r)
    (hRD : ∃ C : ℝ, 0 < C ∧ ∃ d : ℝ, 0 ≤ d ∧
      ∀ r : ℕ, ρ r ≤ C * (1 + (r : ℝ)) ^ d)
    (hvolume : ∀ r, ((subgroupBall L H r).card : ℝ) ≤ (ρ r) ^ 2) : False := by
  obtain ⟨C, hC, d, hd, hbound⟩ := hRD
  exact no_confined_subgroup_of_trivial_radical_srd_volume L hR H P hP hconf
    ρ hρ (ordinarySRD_of_polynomial_bound ρ C d hbound) hvolume

end Q1
