import Q1.ConjugacyGrowth
import Q1.PackingObstruction

/-! Integration with the earlier finite-confinement obstruction. The remaining
subgroup-volume/norm input stays explicit and is not relabeled C*-simplicity. -/

namespace Q1

variable {G : Type*} [Group G]

/-- A precise algebraic witness supplying exponential conjugacy growth.
This predicate refers to an actual subgroup and its actual center quotient. -/
def NonFoelnerCenterQuotientWitness (g : G) : Prop :=
  ∃ (A : Subgroup G) (k : ℕ) (_ : 0 < k) (x : Fin k → A) (u : Fin k → G),
    Subgroup.closure (Set.range x) = ⊤ ∧
    (∀ i, (x i : G) = u i * g * (u i)⁻¹) ∧
    ¬ FiniteFoelner (A ⧸ Subgroup.center A)

theorem exponential_conjugacy_growth_of_witness (L : LengthBall G) (g : G)
    (h : NonFoelnerCenterQuotientWitness g) :
    ∃ c δ : ℝ, 0 < c ∧ c ≤ 1 ∧ 0 < δ ∧
      ∀ r : ℕ, c * Real.exp (δ * r) ≤ ((conjugacyBall L g r).card : ℝ) := by
  obtain ⟨A, k, hk, x, u, hgen, hx, hQ⟩ := h
  exact exponential_conjugacy_growth_of_quotient_not_finiteFoelner L g A k hk x u hgen hx hQ

/-- Quotient-center witnesses replace the prior integrated theorem's assumed
exponential growth. The ordinary SRD and subgroup-ball upper bound remain
separate, explicit hypotheses in the original ambient length. -/
theorem no_confined_subgroup_of_quotient_witnesses_and_srd_volume [DecidableEq G]
    (L : LengthBall G) (H : Subgroup G) (P : Finset G)
    (hconf : ConfinedBy H P)
    (hwitness : ∀ g ∈ P, NonFoelnerCenterQuotientWitness g)
    (ρ : ℕ → ℝ) (hρ : ∀ r, 0 ≤ ρ r) (hsrd : OrdinarySRD ρ)
    (hvolume : ∀ r, ((subgroupBall L H r).card : ℝ) ≤ (ρ r) ^ 2) : False := by
  obtain ⟨c, δ, hc, hc1, hδ, hgrowth⟩ := uniform_exponential_constants P
    (fun g r => ((conjugacyBall L g r).card : ℝ))
    (fun g hg => exponential_conjugacy_growth_of_witness L g (hwitness g hg))
  apply no_confined_subgroup_of_exponential_growth_and_srd_volume
    L H P hconf c δ hc hc1 hδ _ ρ hρ hsrd hvolume
  intro g hg r
  have he : conjugacyBall L g r = (L.ball r).image (fun t => t * g * t⁻¹) := by
    ext y
    simp only [conjugacyBall, Finset.mem_image]
  rw [← he]
  exact hgrowth g hg r

end Q1
