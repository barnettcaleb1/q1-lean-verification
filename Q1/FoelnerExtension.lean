import Q1.FoelnerGrowth
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! Finite Følner permanence for extensions, by finite sections and cocycles.
No amenability equivalence or invariant mean is assumed. -/

namespace Q1

variable {G : Type*} [Group G]

theorem mem_leftTranslate_iff (g y : G) (F : Finset G) :
    y ∈ leftTranslate g F ↔ ∃ x ∈ F, g * x = y := by
  classical
  simp only [leftTranslate, Finset.mem_image]

theorem mem_translateBoundary_iff (g y : G) (F : Finset G) :
    y ∈ translateBoundary g F ↔ (∃ x ∈ F, g * x = y) ∧ y ∉ F := by
  classical
  simp only [translateBoundary, Finset.mem_sdiff, leftTranslate, Finset.mem_image]

/-- The section coordinates of a normal-subgroup extension. -/
noncomputable def extensionPair (N : Subgroup G) [N.Normal]
    (z : (G ⧸ N) × N) : G := z.1.out * z.2

@[simp] theorem extensionPair_quotient (N : Subgroup G) [N.Normal]
    (z : (G ⧸ N) × N) : QuotientGroup.mk' N (extensionPair N z) = z.1 := by
  have hz : QuotientGroup.mk' N (z.2 : G) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr z.2.property
  simp only [extensionPair, map_mul, hz, mul_one, QuotientGroup.mk'_apply,
    QuotientGroup.out_eq']

/-- Different quotient fibers, or different kernel coordinates, stay distinct. -/
theorem extensionPair_injective (N : Subgroup G) [N.Normal] :
    Function.Injective (extensionPair N) := by
  intro a b hab
  have hq : a.1 = b.1 := by
    have hh := congrArg (QuotientGroup.mk' N) hab
    rw [extensionPair_quotient, extensionPair_quotient] at hh
    exact hh
  obtain ⟨a, x⟩ := a
  obtain ⟨b, y⟩ := b
  dsimp at hq
  subst b
  have hxy : x = y := by
    apply Subtype.ext
    exact mul_left_cancel hab
  subst y
  rfl

/-- The finite union of section fibers with the same finite kernel set. -/
noncomputable def extensionSet (N : Subgroup G) [N.Normal]
    (Q : Finset (G ⧸ N)) (E : Finset N) : Finset G := by
  classical
  exact (Q ×ˢ E).image (extensionPair N)

theorem mem_extensionSet_iff (N : Subgroup G) [N.Normal]
    (Q : Finset (G ⧸ N)) (E : Finset N) (y : G) :
    y ∈ extensionSet N Q E ↔
      ∃ q ∈ Q, ∃ n ∈ E, extensionPair N (q, n) = y := by
  classical
  simp only [extensionSet, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨q, n, ⟨hq, hn⟩, he⟩
    exact ⟨q, hq, n, hn, he⟩
  · rintro ⟨q, hq, n, hn, he⟩
    exact ⟨q, n, ⟨hq, hn⟩, he⟩

@[simp] theorem extensionSet_card (N : Subgroup G) [N.Normal]
    (Q : Finset (G ⧸ N)) (E : Finset N) :
    (extensionSet N Q E).card = Q.card * E.card := by
  classical
  rw [extensionSet, Finset.card_image_of_injective _ (extensionPair_injective N),
    Finset.card_product]

theorem extensionSet_nonempty (N : Subgroup G) [N.Normal]
    {Q : Finset (G ⧸ N)} {E : Finset N} (hQ : Q.Nonempty) (hE : E.Nonempty) :
    (extensionSet N Q E).Nonempty := by
  classical
  exact (hQ.product hE).image _

/-- The correction needed when a left translation changes the chosen section. -/
noncomputable def extensionCocycle (N : Subgroup G) [N.Normal]
    (g : G) (q : G ⧸ N) : N :=
  ⟨((QuotientGroup.mk' N g * q).out)⁻¹ * g * q.out, by
    apply (QuotientGroup.eq_one_iff _).mp
    simp [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk'_apply]⟩

theorem extensionCocycle_identity (N : Subgroup G) [N.Normal]
    (g : G) (q : G ⧸ N) (n : N) :
    g * extensionPair N (q, n) =
      extensionPair N (QuotientGroup.mk' N g * q, extensionCocycle N g q * n) := by
  simp only [extensionPair, extensionCocycle, Subgroup.coe_mul]
  group

/-- The original quotient fibers whose translated quotient leaves the finite set. -/
noncomputable def extensionBad (N : Subgroup G) [N.Normal]
    (g : G) (Q : Finset (G ⧸ N)) : Finset (G ⧸ N) := by
  classical
  exact Q.filter (fun q => QuotientGroup.mk' N g * q ∉ Q)

theorem extensionBad_card_le (N : Subgroup G) [N.Normal]
    (g : G) (Q : Finset (G ⧸ N)) :
    (extensionBad N g Q).card ≤ (translateBoundary (QuotientGroup.mk' N g) Q).card := by
  classical
  apply Finset.card_le_card_of_injOn (fun q => QuotientGroup.mk' N g * q)
  · intro q hq
    change q ∈ extensionBad N g Q at hq
    have hmem : q ∈ Q ∧ QuotientGroup.mk' N g * q ∉ Q := by
      simpa only [extensionBad, Finset.mem_filter] using hq
    exact (mem_translateBoundary_iff _ _ _).mpr ⟨⟨q, hmem.1, rfl⟩, hmem.2⟩
  · exact (mul_right_injective _).injOn

/-- Each boundary point is in a bad quotient fiber or a translated kernel boundary. -/
theorem extensionBoundary_subset [DecidableEq G] (N : Subgroup G) [N.Normal]
    (g : G) (Q : Finset (G ⧸ N)) (E : Finset N) :
    translateBoundary g (extensionSet N Q E) ⊆
      leftTranslate g (extensionSet N (extensionBad N g Q) E) ∪
        Q.biUnion (fun q => (translateBoundary (extensionCocycle N g q) E).image
          (fun n => extensionPair N (QuotientGroup.mk' N g * q, n))) := by
  classical
  intro y hy
  obtain ⟨⟨z, hz, rfl⟩, hout⟩ := (mem_translateBoundary_iff _ _ _).mp hy
  obtain ⟨q, hq, n, hn, rfl⟩ := (mem_extensionSet_iff _ _ _ _).mp hz
  by_cases hgood : QuotientGroup.mk' N g * q ∈ Q
  · apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨q, hq, Finset.mem_image.mpr ⟨extensionCocycle N g q * n, ?_, ?_⟩⟩
    · apply (mem_translateBoundary_iff _ _ _).mpr
      refine ⟨⟨n, hn, rfl⟩, ?_⟩
      intro hmem
      apply hout
      rw [extensionCocycle_identity]
      exact (mem_extensionSet_iff _ _ _ _).mpr
        ⟨QuotientGroup.mk' N g * q, hgood, extensionCocycle N g q * n, hmem, rfl⟩
    · exact (extensionCocycle_identity N g q n).symm
  · apply Finset.mem_union_left
    apply (mem_leftTranslate_iff _ _ _).mpr
    refine ⟨extensionPair N (q, n), ?_, rfl⟩
    apply (mem_extensionSet_iff _ _ _ _).mpr
    refine ⟨q, ?_, n, hn, rfl⟩
    simpa only [extensionBad, Finset.mem_filter] using And.intro hq hgood

/-- Explicit extension boundary estimate, with no uncounted fibers or collisions. -/
theorem extensionBoundary_card_le (N : Subgroup G) [N.Normal]
    (g : G) (Q : Finset (G ⧸ N)) (E : Finset N) :
    (translateBoundary g (extensionSet N Q E)).card ≤
      (translateBoundary (QuotientGroup.mk' N g) Q).card * E.card +
        ∑ q ∈ Q, (translateBoundary (extensionCocycle N g q) E).card := by
  classical
  calc
    _ ≤ _ := Finset.card_le_card (extensionBoundary_subset N g Q E)
    _ ≤ _ := Finset.card_union_le _ _
    _ ≤ (leftTranslate g (extensionSet N (extensionBad N g Q) E)).card +
        ∑ q ∈ Q, ((translateBoundary (extensionCocycle N g q) E).image
          (fun n => extensionPair N (QuotientGroup.mk' N g * q, n))).card :=
      Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ (translateBoundary (QuotientGroup.mk' N g) Q).card * E.card +
        ∑ q ∈ Q, (translateBoundary (extensionCocycle N g q) E).card := by
      apply Nat.add_le_add
      · rw [leftTranslate, Finset.card_image_of_injective _ (mul_right_injective _),
          extensionSet_card]
        exact Nat.mul_le_mul_right _ (extensionBad_card_le N g Q)
      · exact Finset.sum_le_sum (fun _ _ => Finset.card_image_le)

/-- Finite Følner sets pass from a normal kernel and its quotient to the group. -/
theorem finiteFoelner_extension (N : Subgroup G) [N.Normal]
    (hN : FiniteFoelner N) (hQ : FiniteFoelner (G ⧸ N)) : FiniteFoelner G := by
  classical
  intro K ε hε
  obtain ⟨Q, hQne, hQb⟩ := hQ (K.image (QuotientGroup.mk' N)) (ε / 2) (by linarith)
  let C : Finset N := (K ×ˢ Q).image (fun z => extensionCocycle N z.1 z.2)
  obtain ⟨E, hEne, hEb⟩ := hN C (ε / 2) (by linarith)
  refine ⟨extensionSet N Q E, extensionSet_nonempty N hQne hEne, ?_⟩
  intro g hg
  have hquot := hQb (QuotientGroup.mk' N g) (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  have hkernel : ∀ q ∈ Q,
      ((translateBoundary (extensionCocycle N g q) E).card : ℝ) ≤ ε / 2 * E.card := by
    intro q hq
    exact hEb _ (Finset.mem_image.mpr ⟨(g, q), Finset.mem_product.mpr ⟨hg, hq⟩, rfl⟩)
  have hsum : (∑ q ∈ Q, ((translateBoundary (extensionCocycle N g q) E).card : ℝ)) ≤
      (Q.card : ℝ) * (ε / 2 * E.card) := by
    simpa using Finset.sum_le_sum hkernel
  have hcount : ((translateBoundary g (extensionSet N Q E)).card : ℝ) ≤
      (translateBoundary (QuotientGroup.mk' N g) Q).card * (E.card : ℝ) +
        ∑ q ∈ Q, ((translateBoundary (extensionCocycle N g q) E).card : ℝ) := by
    exact_mod_cast extensionBoundary_card_le N g Q E
  rw [extensionSet_card, Nat.cast_mul]
  have hprod := mul_le_mul_of_nonneg_right hquot (Nat.cast_nonneg E.card)
  nlinarith

end Q1
