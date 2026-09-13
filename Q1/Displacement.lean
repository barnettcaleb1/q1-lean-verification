import Q1.Action
import Q1.Sunflower
import Mathlib.Tactic

/-!
Finite combinatorial core of Lemma 3 in the frozen BATCH-0003 proof.
The orbit-growth hypothesis here is an explicit finite cardinal threshold.
The conversion from exponential growth to a logarithmic choice of `A` is a
separate obligation, as is constructing `LengthBall` from a generating set.
-/

namespace Q1

variable {G α : Type*} [Group G] [MulAction G α]
  [DecidableEq α]

/-- Every point has a representative from the fixed roots of length at most `B`. -/
def RepresentedWithin (L : LengthBall G) (P Q : Finset α) (B : ℕ) : Prop :=
  ∀ x ∈ Q, ∃ t : G, ∃ x₀ ∈ P, L.length t ≤ B ∧ x = t • x₀

omit [DecidableEq α] in
theorem representedWithin_self (L : LengthBall G) (P : Finset α) :
    RepresentedWithin L P P 0 := by
  intro x hx
  exact ⟨1, x, hx, by simp [L.length_one], by simp⟩

theorem representedWithin_image (L : LengthBall G) (P Q : Finset α)
    (B r : ℕ) (u : G) (hu : L.length u ≤ r)
    (hQ : RepresentedWithin L P Q B) :
    RepresentedWithin L P (imageBlock u Q) (r + B) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨t, x₀, hx₀, ht, rfl⟩ := hQ y hy
  exact ⟨u * t, x₀, hx₀, (L.length_mul u t).trans (Nat.add_le_add hu ht),
    (mul_smul u t x₀).symm⟩

omit [DecidableEq α] in
theorem representedWithin_mono (L : LengthBall G) (P Q Q' : Finset α)
    (B : ℕ) (h : Q' ⊆ Q) (hQ : RepresentedWithin L P Q B) :
    RepresentedWithin L P Q' B := by
  intro x hx
  exact hQ x (h hx)

/-- The exact recurrence used when the sunflower core becomes smaller. -/
theorem displacement_cost (k ℓ B A : ℕ) (hℓ : ℓ < k) :
    (2 ^ ℓ - 1) * (2 * B + A + A) + (B + A) ≤
      (2 ^ k - 1) * (B + A) := by
  have hpow : 2 ^ (ℓ + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hℓ
  have hpos : 1 ≤ 2 ^ ℓ := Nat.one_le_pow _ _ (by omega)
  have hkpos : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by omega)
  rw [pow_succ] at hpow
  have hsub : 2 ^ ℓ - 1 + 1 = 2 ^ ℓ := Nat.sub_add_cancel hpos
  have hksub : 2 ^ k - 1 + 1 = 2 ^ k := Nat.sub_add_cancel hkpos
  nlinarith

/-- Monotonicity of the elementary finite sunflower threshold. -/
theorem sunflower_threshold_mono (k m n : ℕ) (hkm : k ≤ m) (hn : 1 ≤ n) :
    k * (k.factorial * n ^ k) ≤ m * (m.factorial * n ^ m) := by
  exact Nat.mul_le_mul hkm
    (Nat.mul_le_mul (Nat.factorial_le hkm) (Nat.pow_le_pow_right hn hkm))

/-- Finite-threshold version of quantitative displacement (frozen Lemma 3).

The rooted orbit-cardinality hypothesis is retained explicitly. No amenability,
conjugacy-growth theorem, exponential-to-logarithmic conversion or SRD claim is
hidden in this statement.
-/
theorem finite_threshold_displacement (L : LengthBall G) (P F : Finset α)
    (m A : ℕ) (hF : 1 ≤ F.card)
    (hgrowth : ∀ x ∈ P, m * (m.factorial * F.card ^ m) < (orbitBall L A x).card)
    (Q : Finset α) (hQm : Q.card ≤ m) (B : ℕ)
    (hQ : RepresentedWithin L P Q B) :
    ∃ z : G, L.length z ≤ (2 ^ Q.card - 1) * (B + A) ∧
      Disjoint (imageBlock z Q) F := by
  classical
  have aux : ∀ k : ℕ, ∀ Q : Finset α, Q.card = k → k ≤ m → ∀ B : ℕ,
      RepresentedWithin L P Q B →
      ∃ z : G, L.length z ≤ (2 ^ k - 1) * (B + A) ∧
        Disjoint (imageBlock z Q) F := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro Q hcard hkm B hrepr
      by_cases hk : k = 0
      · have hQempty : Q = ∅ := Finset.card_eq_zero.mp (hcard.trans hk)
        refine ⟨1, ?_, ?_⟩
        · simp [L.length_one, hk]
        · simp [hQempty, imageBlock]
      have hkpos : 1 ≤ k := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
      obtain ⟨t, x₀, hx₀, ht, hxt⟩ := hrepr x hx
      let family := (L.ball (B + A)).image (fun u => imageBlock u Q)
      have hfamilycard : ∀ D ∈ family, D.card = k := by
        intro D hD
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hD
        simpa only [card_imageBlock] using hcard
      have hcount : (orbitBall L A x₀).card ≤ family.card * k := by
        calc
          (orbitBall L A x₀).card ≤ (orbitBall L (B + A) x).card :=
            Finset.card_le_card (orbitBall_transfer_of_le L A B hxt ht)
          _ ≤ family.card * Q.card := orbitBall_card_le_imageBlocks L (B + A) Q hx
          _ = family.card * k := by rw [hcard]
      have hlarge : k.factorial * F.card ^ k < family.card := by
        have hg := hgrowth x₀ hx₀
        have hmono := sunflower_threshold_mono k m F.card hkm hF
        by_contra hbad
        have hbad' : family.card ≤ k.factorial * F.card ^ k := by omega
        have hb := Nat.mul_le_mul_right k hbad'
        nlinarith
      obtain ⟨sf, C, hsf, hsfcard, hCcard, hflower, hCsub⟩ :=
        exists_sunflower k F.card hkpos hF family hfamilycard hlarge
      obtain ⟨D₀, hD₀⟩ := Finset.card_pos.mp (by omega : 0 < sf.card)
      obtain ⟨u₀, hu₀, heq₀⟩ := Finset.mem_image.mp (hsf hD₀)
      have hu₀len : L.length u₀ ≤ B + A := (L.mem_ball _ _).mp hu₀
      have hCrepr : RepresentedWithin L P C (2 * B + A) := by
        have himg := representedWithin_image L P Q B (B + A) u₀ hu₀len hrepr
        have hCsubset : C ⊆ imageBlock u₀ Q := by
          rw [heq₀]
          exact hCsub D₀ hD₀
        have hh := representedWithin_mono L P (imageBlock u₀ Q) C
          (B + A + B) hCsubset himg
        have he : B + A + B = 2 * B + A := by omega
        simpa only [he] using hh
      obtain ⟨h, hhlen, hhdisj⟩ :=
        ih C.card hCcard C rfl (hCcard.le.trans hkm) (2 * B + A) hCrepr
      have hCinv : Disjoint C (imageBlock h⁻¹ F) := by
        apply (imageBlock_disjoint_iff h C (imageBlock h⁻¹ F)).mp
        simpa using hhdisj
      have hFsmall : (imageBlock h⁻¹ F).card < sf.card := by
        simp only [card_imageBlock]
        omega
      obtain ⟨D, hD, hDdisj⟩ := exists_disjoint_of_sunflower sf C
        (imageBlock h⁻¹ F) hflower hFsmall hCinv
      obtain ⟨u, hu, heq⟩ := Finset.mem_image.mp (hsf hD)
      refine ⟨h * u, ?_, ?_⟩
      · calc
          L.length (h * u) ≤ L.length h + L.length u := L.length_mul _ _
          _ ≤ (2 ^ C.card - 1) * (2 * B + A + A) + (B + A) :=
            Nat.add_le_add hhlen ((L.mem_ball _ _).mp hu)
          _ ≤ (2 ^ k - 1) * (B + A) := displacement_cost k C.card B A hCcard
      · have hd := imageBlock_disjoint h hDdisj
        simpa only [← heq, ← imageBlock_mul, mul_inv_cancel, imageBlock_one] using hd
  exact aux Q.card Q rfl hQm B hQ

/-- Packing at one common radius from the explicit threshold at the largest
forbidden-set size. This integrates the displacement induction with the greedy
packing theorem, including all cross-block disjointness. -/
theorem finite_threshold_packing (L : LengthBall G) (P : Finset α) (N A : ℕ)
    (hgrowth : ∀ x ∈ P,
      P.card * (P.card.factorial * ((N - 1) * P.card) ^ P.card) <
        (orbitBall L A x).card) :
    ∃ t : Fin N → G, (∀ i, L.length (t i) ≤ (2 ^ P.card - 1) * A) ∧
      Pairwise (fun i j => Disjoint (imageBlock (t i) P) (imageBlock (t j) P)) := by
  classical
  apply greedy_disjoint_blocks L P N ((2 ^ P.card - 1) * A)
  intro F hFsize
  by_cases hFempty : F = ∅
  · exact ⟨1, by simp [L.length_one], by simp [hFempty]⟩
  have hFpos : 1 ≤ F.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hFempty)
  have hsmall : ∀ x ∈ P, P.card * (P.card.factorial * F.card ^ P.card) <
      (orbitBall L A x).card := by
    intro x hx
    apply lt_of_le_of_lt _ (hgrowth x hx)
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.pow_le_pow_left hFsize P.card))
  obtain ⟨t, ht, hdisj⟩ := finite_threshold_displacement L P F P.card A hFpos
    hsmall P le_rfl 0 (representedWithin_self L P)
  exact ⟨t, by simpa using ht, hdisj⟩

end Q1
