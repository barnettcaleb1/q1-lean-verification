import Q1.WordLength
import Q1.Conjugation
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Quotient-center conjugacy tuples and finite word-ball bounds

The quotient is the actual group quotient by the center. Generation is an
explicit hypothesis; neither tuple injectivity nor the cardinal bound is assumed.
-/

namespace Q1

section CenterTuple

variable {H : Type*} [Group H] {k : ℕ}

/-- Equality of conjugates is equivalent to commuting with the relative element. -/
theorem conjugate_eq_iff_relative_commutes (a b x : H) :
    a * x * a⁻¹ = b * x * b⁻¹ ↔ x * (a⁻¹ * b) = (a⁻¹ * b) * x := by
  constructor
  · intro h
    calc
      x * (a⁻¹ * b) = a⁻¹ * (a * x * a⁻¹) * b := by group
      _ = a⁻¹ * (b * x * b⁻¹) * b := by rw [h]
      _ = (a⁻¹ * b) * x := by group
  · intro h
    calc
      a * x * a⁻¹ = a * (x * (a⁻¹ * b)) * b⁻¹ := by group
      _ = a * ((a⁻¹ * b) * x) * b⁻¹ := by rw [h]
      _ = b * x * b⁻¹ := by group

/-- All generator coordinates agree exactly when the center-quotient cosets agree. -/
theorem conjugate_generators_eq_iff_mk_eq (x : Fin k → H)
    (hgen : Subgroup.closure (Set.range x) = ⊤) (a b : H) :
    (∀ i, a * x i * a⁻¹ = b * x i * b⁻¹) ↔
      QuotientGroup.mk' (Subgroup.center H) a =
        QuotientGroup.mk' (Subgroup.center H) b := by
  have hc : Subgroup.centralizer (Set.range x) = Subgroup.center H := by
    rw [← Subgroup.centralizer_closure, hgen]
    exact Subgroup.centralizer_univ
  change (∀ i, a * x i * a⁻¹ = b * x i * b⁻¹) ↔
    (a : H ⧸ Subgroup.center H) = (b : H ⧸ Subgroup.center H)
  rw [QuotientGroup.eq, ← hc, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  exact forall_congr' (fun i => conjugate_eq_iff_relative_commutes a b (x i))

/-- A concrete tuple map on the actual center quotient, using a chosen representative. -/
noncomputable def centerConjugacyTuple (x : Fin k → H)
    (q : H ⧸ Subgroup.center H) : Fin k → H :=
  fun i => q.out * x i * q.out⁻¹

theorem centerConjugacyTuple_mk (x : Fin k → H)
    (hgen : Subgroup.closure (Set.range x) = ⊤) (a : H) :
    centerConjugacyTuple x (QuotientGroup.mk' (Subgroup.center H) a) =
      fun i => a * x i * a⁻¹ := by
  funext i
  apply (conjugate_generators_eq_iff_mk_eq x hgen _ a).mpr ?_ i
  exact Quotient.out_eq' _

theorem centerConjugacyTuple_injective (x : Fin k → H)
    (hgen : Subgroup.closure (Set.range x) = ⊤) :
    Function.Injective (centerConjugacyTuple x) := by
  intro q r h
  have he := (conjugate_generators_eq_iff_mk_eq x hgen q.out r.out).mp
    (fun i => congrFun h i)
  simpa only [QuotientGroup.mk'_apply, Quotient.out_eq'] using he

end CenterTuple

section WordImages

variable {H K : Type*} [Group H] [Group K] [DecidableEq K]

/-- Finite word balls commute with a homomorphism, including all shorter words. -/
theorem wordBall_image (f : H →* K) (S : Finset H) (n : ℕ) :
    wordBall (S.image f) n = (wordBall S n).image f := by
  classical
  have liftList : ∀ w : List K, (∀ s ∈ w, s ∈ S.image f) →
      ∃ v : List H, (∀ s ∈ v, s ∈ S) ∧ v.map f = w := by
    intro w
    induction w with
    | nil => exact fun _ => ⟨[], by simp, rfl⟩
    | cons y w ih =>
      intro hw
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (hw y (by simp))
      obtain ⟨v, hv, he⟩ := ih (fun z hz => hw z (List.mem_cons_of_mem _ hz))
      refine ⟨s :: v, ?_, by simp [he]⟩
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hs
      · exact hv z hz
  ext q
  constructor
  · intro hq
    obtain ⟨w, hw, hs, hp⟩ := (mem_wordBall_iff (S.image f) q n).mp hq
    obtain ⟨v, hv, he⟩ := liftList w hs
    refine Finset.mem_image.mpr ⟨v.prod, ?_, ?_⟩
    · apply (mem_wordBall_iff S v.prod n).mpr
      have hlen := congrArg List.length he
      simp only [List.length_map] at hlen
      exact ⟨v, hlen.trans_le hw, hv, rfl⟩
    · rw [map_list_prod, he, hp]
  · intro hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨w, hw, hs, hp⟩ := (mem_wordBall_iff S a n).mp ha
    apply (mem_wordBall_iff (S.image f) (f a) n).mpr
    refine ⟨w.map f, by simpa using hw, ?_, ?_⟩
    · intro y hy
      obtain ⟨s, hs', rfl⟩ := List.mem_map.mp hy
      exact Finset.mem_image.mpr ⟨s, hs s hs', rfl⟩
    · rw [← map_list_prod, hp]

/-- Every quotient word has a lift of no greater intrinsic word length. -/
theorem mem_wordBall_image_lift (f : H →* K) (S : Finset H) (n : ℕ)
    {q : K} (hq : q ∈ wordBall (S.image f) n) :
    ∃ a ∈ wordBall S n, f a = q := by
  classical
  rw [wordBall_image] at hq
  exact Finset.mem_image.mp hq

end WordImages

section LengthBounds

variable {H G : Type*} [Group H] [Group G]

/-- A product of bounded letters has the corresponding ambient length bound. -/
theorem length_map_list_prod_le (L : LengthBall G) (f : H →* G)
    (w : List H) (M : ℕ) (hw : ∀ s ∈ w, L.length (f s) ≤ M) :
    L.length (f w.prod) ≤ M * w.length := by
  induction w with
  | nil => simp [L.length_one]
  | cons s w ih =>
    have hs := hw s (by simp)
    have ht := ih (fun t ht => hw t (List.mem_cons_of_mem s ht))
    simp only [List.prod_cons, map_mul, List.length_cons]
    have hmul := L.length_mul (f s) (f w.prod)
    nlinarith

theorem length_map_wordBall_le (L : LengthBall G) (f : H →* G)
    (S : Finset H) (M n : ℕ) (hS : ∀ s ∈ S, L.length (f s) ≤ M)
    {a : H} (ha : a ∈ wordBall S n) : L.length (f a) ≤ M * n := by
  obtain ⟨w, hw, hs, rfl⟩ := (mem_wordBall_iff S a n).mp ha
  exact (length_map_list_prod_le L f w M (fun s ht => hS s (hs s ht))).trans
    (Nat.mul_le_mul_left M hw)

end LengthBounds

section Alphabets

variable {H : Type*} [Group H] {k : ℕ}

/-- The finite alphabet consisting of the specified tuple and its inverses. -/
noncomputable def tupleAlphabet (x : Fin k → H) : Finset H := by
  classical
  exact Finset.univ.image x ∪ Finset.univ.image (fun i => (x i)⁻¹)

theorem mem_tupleAlphabet (x : Fin k → H) (s : H) :
    s ∈ tupleAlphabet x ↔ (∃ i, x i = s) ∨ ∃ i, (x i)⁻¹ = s := by
  classical
  simp [tupleAlphabet]

theorem tupleAlphabet_inv_mem (x : Fin k → H) {s : H}
    (hs : s ∈ tupleAlphabet x) : s⁻¹ ∈ tupleAlphabet x := by
  rcases (mem_tupleAlphabet x s).mp hs with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact (mem_tupleAlphabet x _).mpr (Or.inr ⟨i, rfl⟩)
  · exact (mem_tupleAlphabet x _).mpr (Or.inl ⟨i, by simp⟩)

theorem tupleAlphabet_generates (x : Fin k → H)
    (hgen : Subgroup.closure (Set.range x) = ⊤) :
    Subgroup.closure (tupleAlphabet x : Set H) = ⊤ := by
  apply le_antisymm le_top
  rw [← hgen]
  apply Subgroup.closure_mono
  rintro s ⟨i, rfl⟩
  exact (mem_tupleAlphabet x _).mpr (Or.inl ⟨i, rfl⟩)

/-- The actual quotient generating alphabet, without selecting quotient representatives. -/
noncomputable def quotientTupleAlphabet (x : Fin k → H) :
    Finset (H ⧸ Subgroup.center H) := by
  classical
  exact (tupleAlphabet x).image (QuotientGroup.mk' (Subgroup.center H))

theorem quotientTupleAlphabet_generates (x : Fin k → H)
    (hgen : Subgroup.closure (Set.range x) = ⊤) :
    Subgroup.closure (quotientTupleAlphabet x : Set (H ⧸ Subgroup.center H)) = ⊤ := by
  classical
  unfold quotientTupleAlphabet
  rw [Finset.coe_image, ← MonoidHom.map_closure, tupleAlphabet_generates x hgen]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem quotientTupleAlphabet_inv_mem (x : Fin k → H)
    {s : H ⧸ Subgroup.center H} (hs : s ∈ quotientTupleAlphabet x) :
    s⁻¹ ∈ quotientTupleAlphabet x := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hs
  exact Finset.mem_image.mpr ⟨a⁻¹, tupleAlphabet_inv_mem x ha, map_inv _ _⟩

end Alphabets

section AmbientBound

variable {G : Type*} [Group G] {k : ℕ}

theorem tupleAlphabet_ambient_length_le (L : LengthBall G) (A : Subgroup G)
    (x : Fin k → A) (M : ℕ) (hM : ∀ i, L.length (x i : G) ≤ M)
    {s : A} (hs : s ∈ tupleAlphabet x) : L.length (s : G) ≤ M := by
  rcases (mem_tupleAlphabet x s).mp hs with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact hM i
  · simpa only [Subgroup.coe_inv, L.length_inv] using hM i

/-- A point of the quotient n-ball has an ambient lift of length at most M*n. -/
theorem quotient_wordBall_bounded_lift (L : LengthBall G) (A : Subgroup G)
    (x : Fin k → A) (M n : ℕ) (hM : ∀ i, L.length (x i : G) ≤ M)
    {q : A ⧸ Subgroup.center A} (hq : q ∈ wordBall (quotientTupleAlphabet x) n) :
    ∃ a : A, L.length (a : G) ≤ M * n ∧
      QuotientGroup.mk' (Subgroup.center A) a = q := by
  classical
  obtain ⟨a, ha, he⟩ := mem_wordBall_image_lift
    (QuotientGroup.mk' (Subgroup.center A)) (tupleAlphabet x) n hq
  exact ⟨a, length_map_wordBall_le L A.subtype (tupleAlphabet x) M n
    (fun s hs => tupleAlphabet_ambient_length_le L A x M hM hs) ha, he⟩

/-- The actual quotient word-ball injects into k copies of one rooted conjugacy ball. -/
theorem quotient_center_wordBall_card_le_conjugacy [DecidableEq G]
    (L : LengthBall G) (A : Subgroup G)
    (x : Fin k → A) (hgen : Subgroup.closure (Set.range x) = ⊤)
    (g : G) (u : Fin k → G)
    (hx : ∀ i, (x i : G) = u i * g * (u i)⁻¹)
    (M D n : ℕ) (hM : ∀ i, L.length (x i : G) ≤ M)
    (hD : ∀ i, L.length (u i) ≤ D) :
    (wordBall (quotientTupleAlphabet x) n).card ≤
      ((L.ball (M * n + D)).image (fun t => t * g * t⁻¹)).card ^ k := by
  classical
  let QB := wordBall (quotientTupleAlphabet x) n
  let C := (L.ball (M * n + D)).image (fun t => t * g * t⁻¹)
  have hlift (q : QB) : ∃ a : A, L.length (a : G) ≤ M * n ∧
      QuotientGroup.mk' (Subgroup.center A) a = q.1 :=
    quotient_wordBall_bounded_lift L A x M n hM q.2
  choose lift hliftlen hlifteq using hlift
  have hcoord (q : QB) (i : Fin k) :
      (lift q : G) * (x i : G) * (lift q : G)⁻¹ ∈ C := by
    refine Finset.mem_image.mpr ⟨(lift q : G) * u i, ?_, ?_⟩
    · exact (L.mem_ball _ _).mpr
        ((L.length_mul _ _).trans (Nat.add_le_add (hliftlen q) (hD i)))
    · rw [hx i]
      group
  let f (q : QB) (i : Fin k) : C :=
    ⟨(lift q : G) * (x i : G) * (lift q : G)⁻¹, hcoord q i⟩
  have hf : Function.Injective f := by
    intro q r he
    have hcoords : ∀ i, lift q * x i * (lift q)⁻¹ = lift r * x i * (lift r)⁻¹ := by
      intro i
      apply Subtype.ext
      exact congrArg (fun z : C => (z : G)) (congrFun he i)
    have hquot := (conjugate_generators_eq_iff_mk_eq x hgen (lift q) (lift r)).mp hcoords
    apply Subtype.ext
    exact (hlifteq q).symm.trans (hquot.trans (hlifteq r))
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] using hcard

end AmbientBound

end Q1
