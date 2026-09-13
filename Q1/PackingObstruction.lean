import Q1.Conjugation
import Q1.GrowthPacking
import Q1.Asymptotic

/-!
An integrated conditional obstruction in the actual group and length.

The two outstanding group/operator-algebraic inputs are explicit hypotheses:
exponential conjugacy growth at the finite roots, and the subgroup-ball bound
by `ρ²`. Confinement is also supplied explicitly. This file does not define a
placeholder for C*-simplicity or assert that the remaining Q1 bridges are proved.
-/

namespace Q1

open Filter
open scoped Topology

variable {G : Type*} [Group G] [DecidableEq G]

/-- Subgroup elements in the original ambient ball; classical membership is
used only to represent this finite set. -/
noncomputable def subgroupBall (L : LengthBall G) (H : Subgroup G) (r : ℕ) : Finset G := by
  classical
  exact (L.ball r).filter (fun x => x ∈ H)

/-- Every conjugated copy of the finite witness meets the subgroup. -/
def ConfinedBy (H : Subgroup G) (P : Finset G) : Prop :=
  ∀ t : G, ∃ x ∈ P, t * x * t⁻¹ ∈ H

/-- Disjoint conjugate blocks give distinct subgroup elements at the same
controlled support radius. This is the direct counting variant recorded at the
end of the frozen written proof. -/
theorem confined_subgroup_ball_card (L : LengthBall G) (H : Subgroup G)
    (P : Finset G) (hconf : ConfinedBy H P) (N R ℓ : ℕ)
    (hP : ∀ x ∈ P, L.length x ≤ ℓ) (t : Fin N → G)
    (ht : ∀ i, L.length (t i) ≤ R)
    (hd : Pairwise (fun i j => Disjoint (conjugateBlock (t i) P)
      (conjugateBlock (t j) P))) :
    N ≤ (subgroupBall L H (2 * R + ℓ)).card := by
  classical
  choose x hxp hxh using (fun i : Fin N => hconf (t i))
  let D := subgroupBall L H (2 * R + ℓ)
  have hmem (i : Fin N) : t i * x i * (t i)⁻¹ ∈ D := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hxh i⟩
    apply conjugateBlock_subset_ball L (t i) P R ℓ (ht i) hP
    exact Finset.mem_image.mpr ⟨x i, hxp i, rfl⟩
  let f : Fin N → D := fun i => ⟨t i * x i * (t i)⁻¹, hmem i⟩
  have hf : Function.Injective f := by
    intro i j heq
    by_contra hij
    have hval : t i * x i * (t i)⁻¹ = t j * x j * (t j)⁻¹ := congrArg Subtype.val heq
    have hi : t i * x i * (t i)⁻¹ ∈ conjugateBlock (t i) P :=
      Finset.mem_image.mpr ⟨x i, hxp i, rfl⟩
    have hj : t i * x i * (t i)⁻¹ ∈ conjugateBlock (t j) P :=
      Finset.mem_image.mpr ⟨x j, hxp j, hval.symm⟩
    exact Finset.disjoint_left.mp (hd hij) hi hj
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Numerical normalization of the subgroup-ball lower bound. -/
theorem one_le_normalized_of_nat_le_sq (N : ℕ) (hN : 0 < N) (a : ℝ)
    (ha : 0 ≤ a) (hbound : (N : ℝ) ≤ a ^ 2) :
    1 ≤ a * Real.sqrt (1 / (N : ℝ)) := by
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hsqrt : Real.sqrt (N : ℝ) ≤ a := by
    simpa only [Real.sqrt_sq ha] using Real.sqrt_le_sqrt hbound
  have hpos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNreal
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  rw [mul_one_div]
  exact (le_div_iff₀ hpos).2 (by simpa using hsqrt)

/-- Complete conditional finite-confinement contradiction.

This theorem still assumes the unformalized exponential conjugacy-growth input
and the amenable-subgroup `ρ²` volume input. It is not an end-to-end Q1 theorem.
-/
theorem no_confined_subgroup_of_exponential_growth_and_srd_volume
    (L : LengthBall G) (H : Subgroup G) (P : Finset G)
    (hconf : ConfinedBy H P) (c δ : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) (hδ : 0 < δ)
    (hgrowth : ∀ x ∈ P, ∀ r : ℕ, c * Real.exp (δ * (r : ℝ)) ≤
      (((L.ball r).image (fun t => t * x * t⁻¹)).card : ℝ))
    (ρ : ℕ → ℝ) (hρ : ∀ r, 0 ≤ ρ r) (hsrd : OrdinarySRD ρ)
    (hvolume : ∀ r : ℕ, ((subgroupBall L H r).card : ℝ) ≤
      (ρ r) ^ 2) : False := by
  classical
  let Lc := conjugationLengthBall L
  have hg : ∀ x ∈ P, ∀ r : ℕ,
      c * Real.exp (δ * (r : ℝ)) ≤ ((orbitBall Lc r x).card : ℝ) := by
    intro x hx r
    simpa only [Lc, conjugation_orbitBall] using hgrowth x hx r
  obtain ⟨hK, hB, hpack⟩ := exponential_growth_logarithmic_packing Lc P c δ hc hc1 hδ hg
  let R := exponentialPackingRadius P.card c δ
  let K := packingLogK P.card δ
  let B := packingLogB P.card c δ
  let ℓ := P.sup L.length
  have hPlen : ∀ x ∈ P, L.length x ≤ ℓ := by
    intro x hx
    exact Finset.le_sup hx
  have hlog : ∀ᶠ N : ℕ in atTop, (R N : ℝ) ≤ K * Real.log (N : ℝ) + B := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact (hpack N hN).1
  apply false_of_srd_packing_lower_bound ρ hρ hsrd R K B hK ℓ 1 hlog
  filter_upwards [eventually_ge_atTop 2] with N hN
  obtain ⟨t, ht, hd⟩ := (hpack N hN).2
  let tG : Fin N → G := fun i => ConjAct.ofConjAct (t i)
  have htG : ∀ i, L.length (tG i) ≤ R N := ht
  have hdG : Pairwise (fun i j => Disjoint (conjugateBlock (tG i) P)
      (conjugateBlock (tG j) P)) := by
    intro i j hij
    simpa only [conjugateBlock, imageBlock, tG, ConjAct.smul_def] using hd hij
  have hcount := confined_subgroup_ball_card L H P hconf N (R N) ℓ hPlen tG htG hdG
  have hcountcast : (N : ℝ) ≤ ((subgroupBall L H (2 * R N + ℓ)).card : ℝ) := by
    exact_mod_cast hcount
  have hcountreal : (N : ℝ) ≤ (ρ (2 * R N + ℓ)) ^ 2 :=
    hcountcast.trans (hvolume (2 * R N + ℓ))
  simpa only [Nat.cast_one] using
    one_le_normalized_of_nat_le_sq N (by omega) (ρ (2 * R N + ℓ))
      (hρ (2 * R N + ℓ)) hcountreal

end Q1
