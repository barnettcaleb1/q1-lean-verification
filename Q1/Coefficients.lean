import Q1.Action
import Mathlib.Tactic

/-!
Exact finite coefficient accounting for disjoint translated blocks.
This is coefficient arithmetic, not a construction of the reduced group algebra
or a proof of its operator-norm estimate.
-/

namespace Q1

variable {G α : Type*} [Group G] [MulAction G α] [DecidableEq α]

/-- Number of blocks contributing to a point. Each action map is injective, so
membership in one block contributes exactly once in the original double sum. -/
def blockMultiplicity {N : ℕ} (t : Fin N → G) (P : Finset α) (x : α) : ℕ :=
  (Finset.univ.filter (fun i => x ∈ imageBlock (t i) P)).card

/-- The block count equals the full pair-fiber count in the original double sum.
In particular no within-block or cross-block multiplicity has been discarded. -/
theorem blockMultiplicity_eq_pair_count {N : ℕ} (t : Fin N → G)
    (P : Finset α) (x : α) :
    blockMultiplicity t P x =
      ((Finset.univ.product P).filter (fun p : Fin N × α => t p.1 • p.2 = x)).card := by
  classical
  let D := (Finset.univ.product P).filter (fun p : Fin N × α => t p.1 • p.2 = x)
  have hinj : Set.InjOn (Prod.fst : Fin N × α → Fin N) D := by
    intro a ha b hb hab
    apply Prod.ext hab
    apply MulAction.injective (t a.1)
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    simpa only [hab] using ha'.trans hb'.symm
  have himage : D.image Prod.fst =
      Finset.univ.filter (fun i => x ∈ imageBlock (t i) P) := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_imageBlock]
    constructor
    · rintro ⟨⟨j, y⟩, hmem, hji⟩
      change j = i at hji
      subst j
      have hm := Finset.mem_filter.mp hmem
      exact ⟨y, (Finset.mem_product.mp hm.1).2, hm.2⟩
    · rintro ⟨y, hy, hxy⟩
      exact ⟨(i, y), Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, hy⟩, hxy⟩, rfl⟩
  rw [← Finset.card_image_iff.mpr hinj]
  exact congrArg Finset.card himage.symm

/-- For nonempty blocks the translating elements themselves are distinct. -/
theorem translators_injective {N : ℕ} (t : Fin N → G) (P : Finset α)
    (hP : P.Nonempty)
    (hd : Pairwise (fun i j => Disjoint (imageBlock (t i) P) (imageBlock (t j) P))) :
    Function.Injective t := by
  intro i j ht
  by_contra hij
  obtain ⟨x, hx⟩ := hP
  have hi : t i • x ∈ imageBlock (t i) P := mem_imageBlock.mpr ⟨x, hx, rfl⟩
  have hj : t i • x ∈ imageBlock (t j) P := by simpa only [ht] using hi
  exact Finset.disjoint_left.mp (hd hij) hi hj

theorem blockMultiplicity_le_one {N : ℕ} (t : Fin N → G) (P : Finset α)
    (hd : Pairwise (fun i j => Disjoint (imageBlock (t i) P) (imageBlock (t j) P)))
    (x : α) : blockMultiplicity t P x ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  by_contra hij
  exact Finset.disjoint_left.mp (hd hij)
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

theorem blockMultiplicity_eq_one {N : ℕ} (t : Fin N → G) (P : Finset α)
    (hd : Pairwise (fun i j => Disjoint (imageBlock (t i) P) (imageBlock (t j) P)))
    {x : α} (hx : x ∈ blockUnion t P) : blockMultiplicity t P x = 1 := by
  have hle := blockMultiplicity_le_one t P hd x
  have hpos : 0 < blockMultiplicity t P x := by
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hx⟩⟩
  omega

theorem blockMultiplicity_eq_zero {N : ℕ} (t : Fin N → G) (P : Finset α)
    {x : α} (hx : x ∉ blockUnion t P) : blockMultiplicity t P x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact hx (Finset.mem_biUnion.mpr
    ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩)

/-- Coefficient of the average with weight `1/N` on each translating element. -/
noncomputable def uniformBlockCoefficient {N : ℕ} (t : Fin N → G)
    (P : Finset α) (x : α) : ℝ := blockMultiplicity t P x / (N : ℝ)

theorem uniformBlockCoefficient_on_union {N : ℕ} (t : Fin N → G) (P : Finset α)
    (hd : Pairwise (fun i j => Disjoint (imageBlock (t i) P) (imageBlock (t j) P)))
    {x : α} (hx : x ∈ blockUnion t P) :
    uniformBlockCoefficient t P x = 1 / (N : ℝ) := by
  simp only [uniformBlockCoefficient, blockMultiplicity_eq_one t P hd hx, Nat.cast_one]

theorem uniformBlockCoefficient_off_union {N : ℕ} (t : Fin N → G) (P : Finset α)
    {x : α} (hx : x ∉ blockUnion t P) : uniformBlockCoefficient t P x = 0 := by
  simp only [uniformBlockCoefficient, blockMultiplicity_eq_zero t P hx, Nat.cast_zero,
    zero_div]

/-- All cross-collisions are accounted for: exactly `N * P.card` coefficients
are `1/N`, hence the squared coefficient norm is `P.card/N`. -/
theorem uniformBlockCoefficient_energy {N : ℕ} (hN : 0 < N)
    (t : Fin N → G) (P : Finset α)
    (hd : Pairwise (fun i j => Disjoint (imageBlock (t i) P) (imageBlock (t j) P))) :
    ∑ x ∈ blockUnion t P, (uniformBlockCoefficient t P x) ^ 2 =
      (P.card : ℝ) / (N : ℝ) := by
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  calc
    ∑ x ∈ blockUnion t P, (uniformBlockCoefficient t P x) ^ 2 =
        ∑ _x ∈ blockUnion t P, (1 / (N : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [uniformBlockCoefficient_on_union t P hd hx]
    _ = ((N * P.card : ℕ) : ℝ) * (1 / (N : ℝ)) ^ 2 := by
      simp [card_blockUnion t P hd]
    _ = (P.card : ℝ) / (N : ℝ) := by
      push_cast
      field_simp

end Q1
