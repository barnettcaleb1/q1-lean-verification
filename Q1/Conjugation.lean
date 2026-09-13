import Q1.Coefficients
import Q1.Displacement
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! Explicit interpretation of the action lemmas as conjugation in the same
group and finite-ball length. No group-theoretic growth result is imported. -/

namespace Q1

variable {G : Type*} [Group G] [DecidableEq G]

/-- Transport the identical length and balls to the conjugation-action type. -/
noncomputable def conjugationLengthBall (L : LengthBall G) : LengthBall (ConjAct G) := by
  classical
  exact {
    length := fun g => L.length (ConjAct.ofConjAct g)
    length_one := by simpa using L.length_one
    length_mul := by
      intro g h
      simpa using L.length_mul (ConjAct.ofConjAct g) (ConjAct.ofConjAct h)
    length_inv := by intro g; simpa using L.length_inv (ConjAct.ofConjAct g)
    ball := fun r => (L.ball r).image ConjAct.toConjAct
    mem_ball := by
      intro g r
      simp only [Finset.mem_image, L.mem_ball]
      constructor
      · rintro ⟨h, hh, rfl⟩
        simpa using hh
      · intro hg
        exact ⟨ConjAct.ofConjAct g, hg, ConjAct.toConjAct_ofConjAct g⟩ }

omit [DecidableEq G] in
@[simp] theorem conjugationLengthBall_length (L : LengthBall G) (g : ConjAct G) :
    (conjugationLengthBall L).length g = L.length (ConjAct.ofConjAct g) := rfl

/-- An actual conjugated finite block. -/
def conjugateBlock (g : G) (P : Finset G) : Finset G :=
  P.image (fun x => g * x * g⁻¹)

theorem imageBlock_toConjAct (g : G) (P : Finset G) :
    imageBlock (ConjAct.toConjAct g) P = conjugateBlock g P := rfl

theorem conjugation_orbitBall (L : LengthBall G) (r : ℕ) (x : G) :
    orbitBall (conjugationLengthBall L) r x =
      (L.ball r).image (fun t => t * x * t⁻¹) := by
  classical
  simp [orbitBall, conjugationLengthBall, Finset.image_image, Function.comp_def,
    ConjAct.toConjAct_smul]

omit [DecidableEq G] in
theorem conjugate_length_le (L : LengthBall G) (t x : G) :
    L.length (t * x * t⁻¹) ≤ 2 * L.length t + L.length x := by
  have h₁ := L.length_mul (t * x) t⁻¹
  have h₂ := L.length_mul t x
  rw [L.length_inv] at h₁
  omega

/-- The support radius is measured in the original length. -/
theorem conjugateBlock_subset_ball (L : LengthBall G) (t : G) (P : Finset G)
    (R ℓ : ℕ) (ht : L.length t ≤ R) (hP : ∀ x ∈ P, L.length x ≤ ℓ) :
    conjugateBlock t P ⊆ L.ball (2 * R + ℓ) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  apply (L.mem_ball _ _).mpr
  exact (conjugate_length_le L t x).trans (by have := hP x hx; omega)

end Q1
