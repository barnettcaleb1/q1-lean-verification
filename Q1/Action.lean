import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Fin

/-!
# Finite length balls, action images, and greedy disjoint packing

`LengthBall` is an explicit finite-ball hypothesis.  This file does not construct
it from a finite generating set, nor import any analytic or amenability axiom.
-/

namespace Q1

universe u v

/-- A finite subadditive symmetric natural-number length-ball interface. -/
structure LengthBall (G : Type u) [Group G] where
  length : G → ℕ
  length_one : length 1 = 0
  length_mul : ∀ g h, length (g * h) ≤ length g + length h
  length_inv : ∀ g, length g⁻¹ = length g
  ball : ℕ → Finset G
  mem_ball : ∀ g r, g ∈ ball r ↔ length g ≤ r

variable {G : Type u} {α : Type v} [Group G] [MulAction G α]
variable [DecidableEq α]

/-- The image of a finite set under a group element. -/
def imageBlock (g : G) (Q : Finset α) : Finset α :=
  Q.image (fun x => g • x)

@[simp] theorem mem_imageBlock {g : G} {Q : Finset α} {x : α} :
    x ∈ imageBlock g Q ↔ ∃ y ∈ Q, g • y = x := by
  simp [imageBlock]

@[simp] theorem card_imageBlock (g : G) (Q : Finset α) :
    (imageBlock g Q).card = Q.card :=
  Finset.card_image_of_injective Q (MulAction.injective g)

@[simp] theorem imageBlock_one (Q : Finset α) : imageBlock (1 : G) Q = Q := by
  simp [imageBlock]

theorem imageBlock_mul (g h : G) (Q : Finset α) :
    imageBlock (g * h) Q = imageBlock g (imageBlock h Q) := by
  simp [imageBlock, Finset.image_image, Function.comp_def, mul_smul]

@[simp] theorem imageBlock_inv (g : G) (Q : Finset α) :
    imageBlock g⁻¹ (imageBlock g Q) = Q := by
  rw [← imageBlock_mul, inv_mul_cancel, imageBlock_one]

@[simp] theorem imageBlock_inv' (g : G) (Q : Finset α) :
    imageBlock g (imageBlock g⁻¹ Q) = Q := by
  rw [← imageBlock_mul, mul_inv_cancel, imageBlock_one]

theorem imageBlock_disjoint_iff (g : G) (P Q : Finset α) :
    Disjoint (imageBlock g P) (imageBlock g Q) ↔ Disjoint P Q :=
  Finset.disjoint_image (MulAction.injective g)

theorem imageBlock_disjoint (g : G) {P Q : Finset α} (h : Disjoint P Q) :
    Disjoint (imageBlock g P) (imageBlock g Q) :=
  (imageBlock_disjoint_iff g P Q).2 h

theorem imageBlock_mono (g : G) {P Q : Finset α} (h : P ⊆ Q) :
    imageBlock g P ⊆ imageBlock g Q :=
  Finset.image_subset_image h

/-- A rooted orbit ball, without any assertion that moving the root is an isometry. -/
def orbitBall (L : LengthBall G) (r : ℕ) (x : α) : Finset α :=
  (L.ball r).image (fun g => g • x)

@[simp] theorem mem_orbitBall {L : LengthBall G} {r : ℕ} {x y : α} :
    y ∈ orbitBall L r x ↔ ∃ g, L.length g ≤ r ∧ g • x = y := by
  simp [orbitBall, L.mem_ball]

theorem orbitBall_mono (L : LengthBall G) {r s : ℕ} (hrs : r ≤ s) (x : α) :
    orbitBall L r x ⊆ orbitBall L s x := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := mem_orbitBall.mp hy
  exact mem_orbitBall.mpr ⟨g, hg.trans hrs, rfl⟩

/-- Moving a root costs the length of a representing element, additively. -/
theorem orbitBall_transfer (L : LengthBall G) (A : ℕ) {x x₀ : α} {t : G}
    (hx : x = t • x₀) :
    orbitBall L A x₀ ⊆ orbitBall L (A + L.length t) x := by
  intro y hy
  obtain ⟨s, hs, rfl⟩ := mem_orbitBall.mp hy
  refine mem_orbitBall.mpr ⟨s * t⁻¹, ?_, ?_⟩
  · calc
      L.length (s * t⁻¹) ≤ L.length s + L.length t⁻¹ := L.length_mul _ _
      _ = L.length s + L.length t := by rw [L.length_inv]
      _ ≤ A + L.length t := Nat.add_le_add_right hs _
  · rw [hx, mul_smul, inv_smul_smul]

theorem orbitBall_transfer_of_le (L : LengthBall G) (A B : ℕ)
    {x x₀ : α} {t : G} (hx : x = t • x₀) (ht : L.length t ≤ B) :
    orbitBall L A x₀ ⊆ orbitBall L (B + A) x := by
  exact (orbitBall_transfer L A hx).trans
    (orbitBall_mono L (by simpa [Nat.add_comm] using Nat.add_le_add_left ht A) x)

/-- A rooted orbit is covered by the distinct translated blocks containing its root. -/
theorem orbitBall_subset_imageBlocks_union (L : LengthBall G) (r : ℕ)
    (Q : Finset α) {x : α} (hx : x ∈ Q) :
    orbitBall L r x ⊆
      ((L.ball r).image (fun g => imageBlock g Q)).biUnion id := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := mem_orbitBall.mp hy
  refine Finset.mem_biUnion.mpr ⟨imageBlock g Q, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨g, (L.mem_ball g r).2 hg, rfl⟩
  · exact mem_imageBlock.mpr ⟨x, hx, rfl⟩

/-- The cardinality bridge from rooted orbit volume to the family of distinct blocks. -/
theorem orbitBall_card_le_imageBlocks (L : LengthBall G) (r : ℕ)
    (Q : Finset α) {x : α} (hx : x ∈ Q) :
    (orbitBall L r x).card ≤
      ((L.ball r).image (fun g => imageBlock g Q)).card * Q.card := by
  let B := (L.ball r).image (fun g => imageBlock g Q)
  have hcard (q : Finset α) (hq : q ∈ B) : q.card = Q.card := by
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hq
    exact card_imageBlock g Q
  calc
    (orbitBall L r x).card ≤ (B.biUnion id).card :=
      Finset.card_le_card (orbitBall_subset_imageBlocks_union L r Q hx)
    _ ≤ ∑ q ∈ B, q.card := Finset.card_biUnion_le
    _ = ∑ _q ∈ B, Q.card := Finset.sum_congr rfl hcard
    _ = B.card * Q.card := by simp

/-- The union of a finite indexed collection of translated blocks. -/
def blockUnion {n : ℕ} (t : Fin n → G) (P : Finset α) : Finset α :=
  Finset.univ.biUnion (fun i => imageBlock (t i) P)

theorem imageBlock_subset_blockUnion {n : ℕ} (t : Fin n → G) (P : Finset α)
    (i : Fin n) : imageBlock (t i) P ⊆ blockUnion t P := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩

theorem card_blockUnion_le {n : ℕ} (t : Fin n → G) (P : Finset α) :
    (blockUnion t P).card ≤ n * P.card := by
  calc
    (blockUnion t P).card ≤ ∑ i : Fin n, (imageBlock (t i) P).card :=
      Finset.card_biUnion_le
    _ = n * P.card := by simp

/-- Exact count when all whole blocks, including their cross terms, are disjoint. -/
theorem card_blockUnion {n : ℕ} (t : Fin n → G) (P : Finset α)
    (h : Pairwise (fun i j => Disjoint (imageBlock (t i) P) (imageBlock (t j) P))) :
    (blockUnion t P).card = n * P.card := by
  calc
    (blockUnion t P).card = ∑ i : Fin n, (imageBlock (t i) P).card := by
      apply Finset.card_biUnion
      intro i hi j hj hij
      exact h hij
    _ = n * P.card := by simp

/-- Greedy packing from finite-set displacement at a fixed common radius.

The input displacement hypothesis is explicit: this theorem does not assert it
for arbitrary actions.  Empty blocks and N = 0 are permitted.
-/
theorem greedy_disjoint_blocks (L : LengthBall G) (P : Finset α) (N R : ℕ)
    (hdisp : ∀ F : Finset α, F.card ≤ (N - 1) * P.card →
      ∃ t : G, L.length t ≤ R ∧ Disjoint (imageBlock t P) F) :
    ∃ t : Fin N → G, (∀ i, L.length (t i) ≤ R) ∧
      Pairwise (fun i j => Disjoint (imageBlock (t i) P) (imageBlock (t j) P)) := by
  have haux : ∀ n : ℕ, n ≤ N → ∃ t : Fin n → G,
      (∀ i, L.length (t i) ≤ R) ∧
      Pairwise (fun i j => Disjoint (imageBlock (t i) P) (imageBlock (t j) P)) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨Fin.elim0, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
    | succ n ih =>
      intro hn
      obtain ⟨t, ht, hp⟩ := ih (Nat.le_trans (Nat.le_succ n) hn)
      have hn' : n ≤ N - 1 := Nat.le_sub_one_of_lt (Nat.lt_of_succ_le hn)
      have hF : (blockUnion t P).card ≤ (N - 1) * P.card :=
        (card_blockUnion_le t P).trans (Nat.mul_le_mul_right P.card hn')
      obtain ⟨s, hs, hdis⟩ := hdisp (blockUnion t P) hF
      have hnew (i : Fin n) : Disjoint (imageBlock s P) (imageBlock (t i) P) :=
        hdis.mono_right (imageBlock_subset_blockUnion t P i)
      refine ⟨Fin.cons s t, ?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero => simpa using hs
        | succ i => simpa using ht i
      · intro i j hij
        cases i using Fin.cases with
        | zero =>
          cases j using Fin.cases with
          | zero => exact (hij rfl).elim
          | succ j => simpa using hnew j
        | succ i =>
          cases j using Fin.cases with
          | zero => simpa using (hnew i).symm
          | succ j =>
            exact hp (fun h => hij (congrArg Fin.succ h))
  exact haux N le_rfl

end Q1
