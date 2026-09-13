import Q1.FoelnerMean
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-! The converse finite Følner criterion for the exact invariant set probability
used by `HasInvariantMean`. The proof uses Hall's theorem and finite additivity;
no bounded-functional amenability convention is substituted. -/

open scoped Pointwise ENNReal

namespace Q1

variable {G : Type*} [Group G]

/-- An injective map that uses finitely many left translations preserves every
finitely additive left-invariant set function on its domain. -/
theorem mean_image_eq_of_piecewise_leftTranslate
    (m : Set G → ℝ≥0∞) (hm0 : m ∅ = 0)
    (hadd : ∀ A B, Disjoint A B → m (A ∪ B) = m A + m B)
    (hinv : ∀ (g : G) (A : Set G), m (g • A) = m A)
    (f : G → G) (hf : Function.Injective f) (K : Finset G)
    (A : Set G) (hK : ∀ x ∈ A, ∃ k ∈ K, f x = k * x) :
    m (f '' A) = m A := by
  classical
  induction K using Finset.induction_on generalizing A with
  | empty =>
    have hA : A = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      simpa using hK x hx
    simp [hA, hm0]
  | @insert k K hk ih =>
    let B : Set G := {x ∈ A | f x = k * x}
    let C : Set G := A \ B
    have hBC : B ∪ C = A := by
      dsimp [B, C]
      ext x
      simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_sdiff]
      tauto
    have hd : Disjoint B C := Set.disjoint_sdiff_right
    have hd' : Disjoint (f '' B) (f '' C) := Set.disjoint_image_of_injective hf hd
    have hB : f '' B = k • B := by
      ext y
      simp only [Set.mem_image, Set.mem_smul_set, smul_eq_mul]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, hx.2.symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, hx.2⟩
    have hC : ∀ x ∈ C, ∃ a ∈ K, f x = a * x := by
      intro x hx
      obtain ⟨a, ha, hfa⟩ := hK x hx.1
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact False.elim (hx.2 ⟨hx.1, hfa⟩)
      · exact ⟨a, ha, hfa⟩
    calc
      m (f '' A) = m (f '' B ∪ f '' C) := by rw [← Set.image_union, hBC]
      _ = m (f '' B) + m (f '' C) := hadd _ _ hd'
      _ = m B + m C := by rw [hB, hinv, ih C hC]
      _ = m A := by rw [← hadd _ _ hd, hBC]

/-- A left-invariant probability rules out two disjoint injective copies of the
group when both embeddings use a common finite collection of translations. -/
theorem no_doubling_map_of_hasInvariantMean (hmean : HasInvariantMean G)
    (K : Finset G) (f : G × Bool → G) (hf : Function.Injective f)
    (hK : ∀ p, ∃ k ∈ K, f p = k * p.1) : False := by
  classical
  obtain ⟨m, hm0, hm1, hmle, hadd, hinv⟩ := hmean
  have hmass (b : Bool) : m (Set.range (fun x => f (x, b))) = 1 := by
    rw [← Set.image_univ]
    rw [mean_image_eq_of_piecewise_leftTranslate m hm0 hadd hinv
      (fun x => f (x, b)) (fun x y h => (Prod.mk.inj (hf h)).1) K Set.univ]
    · exact hm1
    · exact fun x _ => hK (x, b)
  have hd : Disjoint (Set.range (fun x => f (x, false)))
      (Set.range (fun x => f (x, true))) := by
    apply Set.disjoint_left.mpr
    rintro y ⟨x, rfl⟩ ⟨z, hz⟩
    have := (Prod.mk.inj (hf hz)).2
    cases this
  have hh := hmle (Set.range (fun x => f (x, false)) ∪
    Set.range (fun x => f (x, true)))
  rw [hadd _ _ hd, hmass, hmass] at hh
  norm_num at hh

/-- Hall's theorem turns doubling of all finite subsets into a two-copy
injective map with finitely many possible left translations. -/
theorem exists_doubling_map_of_finset_expansion [DecidableEq G] (K : Finset G)
    (hdouble : ∀ F : Finset G, 2 * F.card ≤ (K * F).card) :
    ∃ f : G × Bool → G, Function.Injective f ∧
      ∀ p, ∃ k ∈ K, f p = k * p.1 := by
  classical
  let t : G × Bool → Finset G := fun p => K.image (fun k => k * p.1)
  have hHall (A : Finset (G × Bool)) : A.card ≤ (A.biUnion t).card := by
    let F : Finset G := A.image Prod.fst
    have hA : A ⊆ F ×ˢ (Finset.univ : Finset Bool) := by
      intro p hp
      exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, by simp⟩
    have hc : A.card ≤ 2 * F.card := by
      have hh := Finset.card_le_card hA
      simpa [Finset.card_product, Nat.mul_comm] using hh
    have he : A.biUnion t = K * F := by
      ext y
      simp only [Finset.mem_biUnion, t, Finset.mem_image, Finset.mem_mul, F]
      constructor
      · rintro ⟨p, hp, k, hk, rfl⟩
        exact ⟨k, hk, p.1, ⟨p, hp, rfl⟩, rfl⟩
      · rintro ⟨k, hk, x, ⟨p, hp, rfl⟩, rfl⟩
        exact ⟨p, hp, k, hk, rfl⟩
    rw [he]
    exact hc.trans (hdouble F)
  obtain ⟨f, hf, ht⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  refine ⟨f, hf, ?_⟩
  intro p
  obtain ⟨k, hk, he⟩ := Finset.mem_image.mp (ht p)
  exact ⟨k, hk, he.symm⟩

/-- Failure of the one-sided finite Følner condition yields a fixed finite
set whose left products expand every finite subset by a factor greater than one. -/
theorem exists_finset_expansion_of_not_finiteFoelner [DecidableEq G]
    (hnot : ¬ FiniteFoelner G) :
    ∃ S : Finset G, ∃ q : ℝ, 1 < q ∧
      ∀ F : Finset G, q * F.card ≤ ((S * F).card : ℝ) := by
  classical
  unfold FiniteFoelner at hnot
  push Not at hnot
  obtain ⟨K, ε, hε, hbad⟩ := hnot
  let S := insert 1 K
  refine ⟨S, 1 + ε, by linarith, ?_⟩
  intro F
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp
  obtain ⟨g, hg, hbd⟩ := hbad F hF
  have hsub : F ⊆ S * F := by
    intro x hx
    exact Finset.mem_mul.mpr ⟨1, by simp [S], x, hx, one_mul x⟩
  have hbound : translateBoundary g F ⊆ ((S * F) \ F) := by
    intro x hx
    simp only [translateBoundary, leftTranslate, Finset.mem_sdiff, Finset.mem_image] at hx
    obtain ⟨⟨y, hy, rfl⟩, hn⟩ := hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_mul.mpr
      ⟨g, by simp [S, hg], y, hy, rfl⟩, hn⟩
  have hc : ((translateBoundary g F).card : ℝ) ≤ (((S * F) \ F).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hbound
  have he : (((S * F) \ F).card : ℝ) + F.card = ((S * F).card : ℝ) := by
    exact_mod_cast Finset.card_sdiff_add_card_eq_card hsub
  nlinarith

/-- Iterating a uniform finite-set expansion produces a doubling set. -/
theorem exists_finset_doubling_of_not_finiteFoelner [DecidableEq G]
    (hnot : ¬ FiniteFoelner G) :
    ∃ K : Finset G, ∀ F : Finset G, 2 * F.card ≤ (K * F).card := by
  classical
  obtain ⟨S, q, hq, hS⟩ := exists_finset_expansion_of_not_finiteFoelner hnot
  have hpow (n : ℕ) (F : Finset G) : q ^ n * F.card ≤ ((S ^ n * F).card : ℝ) := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        q ^ (n + 1) * F.card = q * (q ^ n * F.card) := by ring
        _ ≤ q * ((S ^ n * F).card : ℝ) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
        _ ≤ ((S * (S ^ n * F)).card : ℝ) := hS _
        _ = ((S ^ (n + 1) * F).card : ℝ) := by rw [pow_succ', mul_assoc]
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 : ℝ) hq
  refine ⟨S ^ n, ?_⟩
  intro F
  have hh := (mul_le_mul_of_nonneg_right hn.le (Nat.cast_nonneg F.card)).trans (hpow n F)
  exact_mod_cast hh

/-- The invariant probability on all subsets gives the exact simultaneous,
one-sided finite Følner condition, for arbitrary groups. -/
theorem finiteFoelner_of_hasInvariantMean (hmean : HasInvariantMean G) :
    FiniteFoelner G := by
  classical
  by_contra hnot
  obtain ⟨K, hK⟩ := exists_finset_doubling_of_not_finiteFoelner hnot
  obtain ⟨f, hf, htrans⟩ := exists_doubling_map_of_finset_expansion K hK
  exact no_doubling_map_of_hasInvariantMean hmean K f hf htrans

theorem hasInvariantMean_iff_finiteFoelner : HasInvariantMean G ↔ FiniteFoelner G :=
  ⟨finiteFoelner_of_hasInvariantMean, hasInvariantMean_of_finiteFoelner⟩

end Q1
