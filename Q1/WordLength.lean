import Q1.Action
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

namespace Q1

variable {G : Type*} [Group G]

/-- Finite enumeration of products of at most n letters from S.
The union with the preceding ball represents shorter words; no identity letter
is added to S. -/
noncomputable def wordBall (S : Finset G) : ℕ → Finset G := by
  classical
  exact fun n => Nat.rec {1}
    (fun _ B => B ∪ S.biUnion (fun s => B.image (fun g => s * g))) n

theorem mem_wordBall_iff (S : Finset G) (g : G) (n : ℕ) :
    g ∈ wordBall S n ↔
      ∃ w : List G, w.length ≤ n ∧ (∀ s ∈ w, s ∈ S) ∧ w.prod = g := by
  classical
  induction n generalizing g with
  | zero =>
    constructor
    · intro hg
      have hg1 : g = 1 := by simpa [wordBall] using hg
      exact ⟨[], by simp, by simp, by simpa using hg1.symm⟩
    · rintro ⟨w, hw, hs, hp⟩
      have he : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
      simp [he] at hp
      simp [wordBall, hp]
  | succ n ih =>
    have hrec : wordBall S (n + 1) =
        wordBall S n ∪ S.biUnion (fun s => (wordBall S n).image (fun h => s * h)) := rfl
    rw [hrec]
    constructor
    · intro hg
      rcases Finset.mem_union.mp hg with hg | hg
      · obtain ⟨w, hw, hs, hp⟩ := (ih g).mp hg
        exact ⟨w, Nat.le_trans hw (Nat.le_succ n), hs, hp⟩
      · obtain ⟨s, hs, hg⟩ := Finset.mem_biUnion.mp hg
        obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hg
        obtain ⟨w, hw, hS, hp⟩ := (ih h).mp hh
        refine ⟨s :: w, by simpa using Nat.add_le_add_right hw 1, ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hs
          · exact hS x hx
        · simp [hp]
    · rintro ⟨w, hw, hs, hp⟩
      cases w with
      | nil =>
        have hg1 : g = 1 := by simpa using hp.symm
        apply Finset.mem_union.mpr
        left
        apply (ih g).mpr
        exact ⟨[], by simp, by simp, by simpa using hg1.symm⟩
      | cons s w =>
        apply Finset.mem_union.mpr
        right
        refine Finset.mem_biUnion.mpr ⟨s, hs s (by simp), ?_⟩
        apply Finset.mem_image.mpr
        refine ⟨w.prod, (ih w.prod).mpr ⟨w, ?_, ?_, rfl⟩, ?_⟩
        · simpa using hw
        · intro x hx
          exact hs x (List.mem_cons_of_mem s hx)
        · simpa using hp

/-- Inverse-closed subgroup generators give an actual finite word for every element. -/
theorem exists_word_of_generates (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    ∃ w : List G, (∀ s ∈ w, s ∈ S) ∧ w.prod = g := by
  classical
  have hg : g ∈ Subgroup.closure (S : Set G) := by
    rw [hgen]
    trivial
  refine Subgroup.closure_induction
    (p := fun g _ => ∃ w : List G, (∀ s ∈ w, s ∈ S) ∧ w.prod = g)
    ?_ ?_ ?_ ?_ hg
  · intro s hs
    exact ⟨[s], by simpa using hs, by simp⟩
  · exact ⟨[], by simp, by simp⟩
  · intro x y hx hy ihx ihy
    obtain ⟨v, hv, hpv⟩ := ihx
    obtain ⟨w, hw, hpw⟩ := ihy
    refine ⟨v ++ w, ?_, ?_⟩
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hv s hs
      · exact hw s hs
    · simp [List.prod_append, hpv, hpw]
  · intro x hx ihx
    obtain ⟨w, hw, hp⟩ := ihx
    refine ⟨(w.map (fun s => s⁻¹)).reverse, ?_, ?_⟩
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hs)
      exact hsym t (hw t ht)
    · rw [← List.prod_inv_reverse, hp]

theorem exists_mem_wordBall (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    ∃ n, g ∈ wordBall S n := by
  obtain ⟨w, hw, hp⟩ := exists_word_of_generates S hsym hgen g
  exact ⟨w.length, (mem_wordBall_iff S g w.length).mpr ⟨w, le_rfl, hw, hp⟩⟩

/-- The least number of letters from the given finite symmetric generating set. -/
noncomputable def wordLength (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) : ℕ := by
  classical
  exact Nat.find (exists_mem_wordBall S hsym hgen g)

theorem wordLength_le_iff (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) (n : ℕ) :
    wordLength S hsym hgen g ≤ n ↔
      ∃ w : List G, w.length ≤ n ∧ (∀ s ∈ w, s ∈ S) ∧ w.prod = g := by
  classical
  constructor
  · intro hle
    have hmem : g ∈ wordBall S (wordLength S hsym hgen g) :=
      Nat.find_spec (exists_mem_wordBall S hsym hgen g)
    obtain ⟨w, hw, hs, hp⟩ := (mem_wordBall_iff S g _).mp hmem
    exact ⟨w, hw.trans hle, hs, hp⟩
  · intro hw
    exact Nat.find_min' (exists_mem_wordBall S hsym hgen g)
      ((mem_wordBall_iff S g n).mpr hw)

theorem wordLength_one (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) :
    wordLength S hsym hgen 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (wordLength_le_iff S hsym hgen 1 0).mpr ⟨[], by simp, by simp, by simp⟩

theorem wordLength_mul (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g h : G) :
    wordLength S hsym hgen (g * h) ≤
      wordLength S hsym hgen g + wordLength S hsym hgen h := by
  obtain ⟨v, hv, hSv, hpv⟩ :=
    (wordLength_le_iff S hsym hgen g _).mp le_rfl
  obtain ⟨w, hw, hSw, hpw⟩ :=
    (wordLength_le_iff S hsym hgen h _).mp le_rfl
  apply (wordLength_le_iff S hsym hgen (g * h) _).mpr
  refine ⟨v ++ w, ?_, ?_, ?_⟩
  · simpa using Nat.add_le_add hv hw
  · intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hSv s hs
    · exact hSw s hs
  · simp [List.prod_append, hpv, hpw]

private theorem wordLength_inv_le (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    wordLength S hsym hgen g⁻¹ ≤ wordLength S hsym hgen g := by
  obtain ⟨w, hw, hS, hp⟩ :=
    (wordLength_le_iff S hsym hgen g _).mp le_rfl
  apply (wordLength_le_iff S hsym hgen g⁻¹ _).mpr
  refine ⟨(w.map (fun s => s⁻¹)).reverse, by simpa using hw, ?_, ?_⟩
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hs)
    exact hsym t (hS t ht)
  · rw [← List.prod_inv_reverse, hp]

theorem wordLength_inv (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    wordLength S hsym hgen g⁻¹ = wordLength S hsym hgen g := by
  apply Nat.le_antisymm (wordLength_inv_le S hsym hgen g)
  simpa using wordLength_inv_le S hsym hgen g⁻¹

/-- The concrete finite symmetric word metric realizes the abstract ball interface. -/
noncomputable def wordLengthBall (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) : LengthBall G where
  length := wordLength S hsym hgen
  length_one := wordLength_one S hsym hgen
  length_mul := wordLength_mul S hsym hgen
  length_inv := wordLength_inv S hsym hgen
  ball := wordBall S
  mem_ball := fun g n => (mem_wordBall_iff S g n).trans
    (wordLength_le_iff S hsym hgen g n).symm

/-- Exact word-list semantics for the exported LengthBall. -/
theorem wordLengthBall_length_le_iff (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) (n : ℕ) :
    (wordLengthBall S hsym hgen).length g ≤ n ↔
      ∃ w : List G, w.length ≤ n ∧ (∀ s ∈ w, s ∈ S) ∧ w.prod = g :=
  wordLength_le_iff S hsym hgen g n

/-- The least length is attained by a word of exactly that length. -/
theorem exists_word_length_eq (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    ∃ w : List G, w.length = (wordLengthBall S hsym hgen).length g ∧
      (∀ s ∈ w, s ∈ S) ∧ w.prod = g := by
  obtain ⟨w, hw, hS, hp⟩ :=
    (wordLengthBall_length_le_iff S hsym hgen g _).mp le_rfl
  refine ⟨w, Nat.le_antisymm hw ?_, hS, hp⟩
  exact (wordLengthBall_length_le_iff S hsym hgen g w.length).mpr
    ⟨w, le_rfl, hS, hp⟩

theorem wordLengthBall_length_eq_zero_iff (S : Finset G)
    (hsym : ∀ s ∈ S, s⁻¹ ∈ S)
    (hgen : Subgroup.closure (S : Set G) = ⊤) (g : G) :
    (wordLengthBall S hsym hgen).length g = 0 ↔ g = 1 := by
  constructor
  · intro hg
    obtain ⟨w, hw, hS, hp⟩ :=
      (wordLengthBall_length_le_iff S hsym hgen g 0).mp (by omega)
    have he : w = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hw)
    simpa [he] using hp.symm
  · rintro rfl
    exact (wordLengthBall S hsym hgen).length_one

end Q1
