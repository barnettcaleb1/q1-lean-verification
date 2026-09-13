import Q1.WordLength
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Finite-set Følner conditions and fixed-generator word-ball expansion.
This defines an explicit finite combinatorial property; it does not silently
identify that property with an amenable-radical or invariant-mean API. -/

namespace Q1

variable {G : Type*} [Group G]

noncomputable def leftTranslate (g : G) (F : Finset G) : Finset G := by
  classical
  exact F.image (g * ·)

noncomputable def translateBoundary (g : G) (F : Finset G) : Finset G := by
  classical
  exact leftTranslate g F \ F

/-- One-sided finite Følner condition, for every finite collection of translations. -/
def FiniteFoelner (G : Type*) [Group G] : Prop :=
  ∀ K : Finset G, ∀ ε : ℝ, 0 < ε → ∃ F : Finset G, F.Nonempty ∧
    ∀ g ∈ K, ((translateBoundary g F).card : ℝ) ≤ ε * F.card

/-- The same approximation restricted to the specified finite alphabet. -/
def GeneratorFoelner (S : Finset G) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ F : Finset G, F.Nonempty ∧
    ∀ g ∈ S, ((translateBoundary g F).card : ℝ) ≤ ε * F.card

@[simp] theorem translateBoundary_one (F : Finset G) : translateBoundary 1 F = ∅ := by
  classical
  simp [translateBoundary, leftTranslate]

/-- Cardinal triangle inequality under multiplication of translations. -/
theorem translateBoundary_mul_card_le (a b : G) (F : Finset G) :
    (translateBoundary (a * b) F).card ≤
      (translateBoundary a F).card + (translateBoundary b F).card := by
  classical
  have hsub : translateBoundary (a * b) F ⊆
      translateBoundary a F ∪ leftTranslate a (translateBoundary b F) := by
    intro x hx
    obtain ⟨hx, hnot⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    by_cases hb : b * y ∈ F
    · apply Finset.mem_union_left
      apply Finset.mem_sdiff.mpr
      exact ⟨Finset.mem_image.mpr ⟨b * y, hb, (mul_assoc _ _ _).symm⟩, hnot⟩
    · apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨b * y, Finset.mem_sdiff.mpr ⟨?_, hb⟩, (mul_assoc _ _ _).symm⟩
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
  calc
    _ ≤ (translateBoundary a F ∪ leftTranslate a (translateBoundary b F)).card :=
      Finset.card_le_card hsub
    _ ≤ (translateBoundary a F).card + (leftTranslate a (translateBoundary b F)).card :=
      Finset.card_union_le _ _
    _ = _ := by rw [leftTranslate, Finset.card_image_of_injective _ (mul_right_injective a)]

/-- The translation loss of a word is bounded by its length times the generator loss. -/
theorem translateBoundary_word_card_le (S F : Finset G) (ε : ℝ)
    (_hε : 0 ≤ ε) (hS : ∀ g ∈ S, ((translateBoundary g F).card : ℝ) ≤ ε * F.card)
    (w : List G) (hw : ∀ g ∈ w, g ∈ S) :
    ((translateBoundary w.prod F).card : ℝ) ≤ (w.length : ℝ) * ε * F.card := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have ha := hS a (hw a (by simp))
    have hh := ih (fun g hg => hw g (by simp [hg]))
    have hc : ((translateBoundary (a * w.prod) F).card : ℝ) ≤
        (translateBoundary a F).card + (translateBoundary w.prod F).card := by
      exact_mod_cast translateBoundary_mul_card_le a w.prod F
    simp only [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- For a finite symmetric generating set, testing its generators suffices. -/
theorem finiteFoelner_of_generatorFoelner (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (h : GeneratorFoelner S) : FiniteFoelner G := by
  classical
  intro K ε hε
  let L := wordLengthBall S hsym hgen
  let R := K.sup L.length + 1
  have hR : (0 : ℝ) < R := by dsimp [R]; positivity
  obtain ⟨F, hF, hS⟩ := h (ε / R) (div_pos hε hR)
  refine ⟨F, hF, ?_⟩
  intro g hg
  obtain ⟨w, hw, hwS, hprod⟩ := exists_word_length_eq S hsym hgen g
  have hlen : w.length ≤ R := by
    rw [hw]
    exact (Finset.le_sup (f := L.length) hg).trans (Nat.le_succ _)
  have hc := translateBoundary_word_card_le S F (ε / R) (div_nonneg hε.le hR.le) hS w hwS
  rw [hprod] at hc
  have hlenr : (w.length : ℝ) ≤ R := by exact_mod_cast hlen
  have hprodle : (w.length : ℝ) * (ε / R) ≤ ε := by
    have hh := mul_le_mul_of_nonneg_right hlenr (div_nonneg hε.le hR.le)
    have he : (R : ℝ) * (ε / R) = ε := by field_simp
    rwa [he] at hh
  exact hc.trans (mul_le_mul_of_nonneg_right hprodle (Nat.cast_nonneg _))

theorem finiteFoelner_iff_generatorFoelner (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤) :
    FiniteFoelner G ↔ GeneratorFoelner S := by
  constructor
  · intro h
    exact h S
  · exact finiteFoelner_of_generatorFoelner S hsym hgen

noncomputable def generatorBoundary (S F : Finset G) : Finset G := by
  classical
  exact (S.biUnion (fun s => leftTranslate s F)) \ F

theorem translateBoundary_subset_generatorBoundary (S F : Finset G) (s : G) (hs : s ∈ S) :
    translateBoundary s F ⊆ generatorBoundary S F := by
  classical
  intro x hx
  obtain ⟨hx, hnot⟩ := Finset.mem_sdiff.mp hx
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr ⟨s, hs, hx⟩, hnot⟩

/-- Failure of the full finite Følner condition forces uniform expansion by
this fixed symmetric generating set. -/
theorem exists_generator_expansion_of_not_finiteFoelner (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hnot : ¬ FiniteFoelner G) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ F : Finset G, F.Nonempty →
      ε * F.card ≤ (generatorBoundary S F).card := by
  classical
  have hbad : ¬ GeneratorFoelner S := fun h =>
    hnot (finiteFoelner_of_generatorFoelner S hsym hgen h)
  unfold GeneratorFoelner at hbad
  push Not at hbad
  obtain ⟨ε, hε, hF⟩ := hbad
  refine ⟨ε, hε, ?_⟩
  intro F hnon
  obtain ⟨s, hs, hlarge⟩ := hF F hnon
  have hc : ((translateBoundary s F).card : ℝ) ≤ (generatorBoundary S F).card := by
    exact_mod_cast Finset.card_le_card (translateBoundary_subset_generatorBoundary S F s hs)
  exact hlarge.le.trans hc

theorem wordBall_nonempty (S : Finset G) (n : ℕ) : (wordBall S n).Nonempty := by
  exact ⟨1, (mem_wordBall_iff S 1 n).mpr ⟨[], by simp, by simp, by simp⟩⟩

/-- The next word ball adds exactly the outside generator boundary. -/
theorem wordBall_succ_card (S : Finset G) (n : ℕ) :
    (wordBall S (n + 1)).card =
      (wordBall S n).card + (generatorBoundary S (wordBall S n)).card := by
  classical
  change (wordBall S n ∪ S.biUnion (fun s => (wordBall S n).image (s * ·))).card = _
  unfold generatorBoundary leftTranslate
  simpa only [Finset.union_comm, Nat.add_comm] using
    (Finset.card_sdiff_add_card (S.biUnion (fun s => (wordBall S n).image (s * ·)))
      (wordBall S n)).symm

/-- Genuine exponential word-ball growth at every natural radius follows from
uniform boundary expansion; this uses no growth-rate dichotomy. -/
theorem exponential_wordBall_of_generator_expansion (S : Finset G) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hexpand : ∀ F : Finset G, F.Nonempty →
      ε * F.card ≤ (generatorBoundary S F).card) :
    ∀ n : ℕ, (1 + ε) ^ n ≤ ((wordBall S n).card : ℝ) := by
  intro n
  induction n with
  | zero => simp [wordBall]
  | succ n ih =>
    have hh := hexpand (wordBall S n) (wordBall_nonempty S n)
    have he : ((wordBall S (n + 1)).card : ℝ) =
        (wordBall S n).card + (generatorBoundary S (wordBall S n)).card := by
      exact_mod_cast wordBall_succ_card S n
    rw [pow_succ]
    have hp := mul_le_mul_of_nonneg_right ih (show 0 ≤ 1 + ε by linarith)
    nlinarith

theorem exponential_wordBall_of_not_finiteFoelner (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S) (hgen : Subgroup.closure (S : Set G) = ⊤)
    (hnot : ¬ FiniteFoelner G) :
    ∃ q : ℝ, 1 < q ∧ ∀ n : ℕ, q ^ n ≤ ((wordBall S n).card : ℝ) := by
  obtain ⟨ε, hε, hexpand⟩ := exists_generator_expansion_of_not_finiteFoelner S hsym hgen hnot
  exact ⟨1 + ε, by linarith, exponential_wordBall_of_generator_expansion S ε hε.le hexpand⟩

end Q1
