import Q1.FoelnerGrowth
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fintype.Pi
import Mathlib.GroupTheory.Subgroup.Center

/-!
# The finite Følner condition for commutative groups

The word-ball estimate counts exponent functions. It only bounds the size of
their image; no injectivity of a box of powers in the group is assumed.
-/

open Filter
open scoped Topology BigOperators

namespace Q1

/-- Products of at most `n` letters in a finite commutative alphabet have at
most `(n+1)^|S|` different exponent vectors. Neither symmetry nor generation
of the ambient group is assumed. -/
theorem wordBall_card_le_pow_card {G : Type*} [CommGroup G]
    (S : Finset G) (n : ℕ) : (wordBall S n).card ≤ (n + 1) ^ S.card := by
  classical
  let evaluate : (S → Fin (n + 1)) → G :=
    fun f => ∏ s : S, (s : G) ^ (f s : ℕ)
  have hsub : wordBall S n ⊆ Finset.univ.image evaluate := by
    intro g hg
    obtain ⟨w, hwlen, hwS, hwprod⟩ := (mem_wordBall_iff S g n).mp hg
    let f : S → Fin (n + 1) := fun s =>
      ⟨w.count (s : G), (show w.count (s : G) ≤ w.length from List.count_le_length).trans_lt
        (hwlen.trans_lt (Nat.lt_succ_self n))⟩
    apply Finset.mem_image.mpr
    refine ⟨f, Finset.mem_univ _, ?_⟩
    have hwsub : w.toFinset ⊆ S := by
      intro s hs
      exact hwS s (List.mem_toFinset.mp hs)
    change (∏ s : S, (s : G) ^ w.count (s : G)) = g
    rw [Finset.prod_coe_sort (s := S) (f := fun x : G => x ^ w.count x)]
    exact (Finset.prod_list_count_of_subset w S hwsub).symm.trans hwprod
  calc
    (wordBall S n).card ≤ (Finset.univ.image evaluate).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (S → Fin (n + 1))).card := Finset.card_image_le
    _ = (n + 1) ^ S.card := by simp

/-- Polynomial word-ball upper growth for a particular finite alphabet prevents
uniform expansion and gives its finite Følner approximation. No symmetry or
generation assumption is used. -/
theorem generatorFoelner_of_polynomial_wordBall {G : Type*} [Group G]
    (S : Finset G) (d : ℕ)
    (hpoly : ∀ n : ℕ, (wordBall S n).card ≤ (n + 1) ^ d) :
    GeneratorFoelner S := by
  classical
  by_contra hbad
  unfold GeneratorFoelner at hbad
  push Not at hbad
  obtain ⟨ε, hε, hF⟩ := hbad
  have hexpand : ∀ F : Finset G, F.Nonempty →
      ε * F.card ≤ (generatorBoundary S F).card := by
    intro F hnon
    obtain ⟨s, hs, hlarge⟩ := hF F hnon
    have hc : ((translateBoundary s F).card : ℝ) ≤ (generatorBoundary S F).card := by
      exact_mod_cast Finset.card_le_card
        (translateBoundary_subset_generatorBoundary S F s hs)
    exact hlarge.le.trans hc
  have hexp := exponential_wordBall_of_generator_expansion S ε hε.le hexpand
  let q : ℝ := 1 + ε
  have hq : 1 < q := by dsimp [q]; linarith
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hlim : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ d / q ^ (n + 1))
      atTop (𝓝 0) :=
    (tendsto_pow_const_div_const_pow_of_one_lt d hq).comp (tendsto_add_atTop_nat 1)
  have hsmall := hlim.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / q by positivity))
  obtain ⟨n, hn⟩ := hsmall.exists
  have hlt := (div_lt_iff₀ (pow_pos hqpos (n + 1))).mp hn
  have heq : (1 / q) * q ^ (n + 1) = q ^ n := by
    rw [pow_succ]
    field_simp
  rw [heq] at hlt
  have hp : ((wordBall S n).card : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ d := by
    exact_mod_cast hpoly n
  exact (not_lt_of_ge ((hexp n).trans hp)) hlt

/-- Every finite set of translations in a commutative group has finite
approximations with arbitrarily small relative one-sided translation boundary. -/
theorem generatorFoelner_of_commutative {G : Type*} [CommGroup G] (S : Finset G) :
    GeneratorFoelner S :=
  generatorFoelner_of_polynomial_wordBall S S.card (wordBall_card_le_pow_card S)

/-- Every commutative group satisfies the explicit finite Følner condition,
without finite-generation or countability assumptions. -/
theorem finiteFoelner_of_commutative (G : Type*) [CommGroup G] : FiniteFoelner G := by
  intro K
  exact generatorFoelner_of_commutative K

open scoped IsMulCommutative in
/-- In particular, the center of any group satisfies the explicit finite
Følner condition, using its actual subgroup group structure. -/
theorem finiteFoelner_center (G : Type*) [Group G] :
    FiniteFoelner (Subgroup.center G) :=
  finiteFoelner_of_commutative (Subgroup.center G)

end Q1
