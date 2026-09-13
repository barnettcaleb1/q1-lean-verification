import Q1.FoelnerLocal
import Q1.ConjugacyTuples

/-! A non-Følner normal closure yields a finite non-Følner subgroup generated
by explicitly enumerated conjugates. This retains every group and conjugator
needed for the subsequent center-quotient growth argument. -/

namespace Q1

variable {G : Type*} [Group G]

noncomputable def finsetClosureTuple (P : Finset G) :
    Fin P.card → Subgroup.closure (↑P : Set G) := fun i =>
  ⟨((P.equivFin).symm i).val, Subgroup.subset_closure ((P.equivFin).symm i).property⟩

theorem finsetClosureTuple_generates (P : Finset G) :
    Subgroup.closure (Set.range (finsetClosureTuple P)) = ⊤ := by
  classical
  let A := Subgroup.closure (↑P : Set G)
  apply Subgroup.map_injective (f := A.subtype) A.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have he : A.subtype '' Set.range (finsetClosureTuple P) = (↑P : Set G) := by
    ext x
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ((P.equivFin).symm i).property
    · intro hx
      let y : P := ⟨x, hx⟩
      refine ⟨finsetClosureTuple P (P.equivFin y), ⟨P.equivFin y, rfl⟩, ?_⟩
      simp [finsetClosureTuple, y]
  rw [he]

theorem finsetClosureTuple_mem (P : Finset G) (i : Fin P.card) :
    (finsetClosureTuple P i : G) ∈ P := ((P.equivFin).symm i).property

/-- The finite-stage step of written Lemma 1, for the actual normal closure
of a singleton and explicit conjugators in the ambient group. -/
theorem exists_conjugate_tuple_not_finiteFoelner (g : G)
    (hnot : ¬ FiniteFoelner (Subgroup.normalClosure ({g} : Set G))) :
    ∃ (A : Subgroup G) (k : ℕ) (_ : 0 < k) (x : Fin k → A) (u : Fin k → G),
      Subgroup.closure (Set.range x) = ⊤ ∧
      (∀ i, (x i : G) = u i * g * (u i)⁻¹) ∧ ¬ FiniteFoelner A := by
  classical
  obtain ⟨P, hne, hP, hbad⟩ := exists_nonempty_not_finiteFoelner_finset_stage
    (Group.conjugatesOfSet ({g} : Set G)) hnot
  let x := finsetClosureTuple P
  have hconj : ∀ i : Fin P.card, ∃ u : G, u * g * u⁻¹ = (x i : G) := by
    intro i
    have hh := hP (finsetClosureTuple_mem P i)
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hh
    have he : a = g := Set.mem_singleton_iff.mp ha
    subst a
    exact isConj_iff.mp hax
  choose u hu using hconj
  exact ⟨Subgroup.closure (↑P : Set G), P.card, hne.card_pos, x, u,
    finsetClosureTuple_generates P, fun i => (hu i).symm, hbad⟩

end Q1
