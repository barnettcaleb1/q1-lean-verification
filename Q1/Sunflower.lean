import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

namespace Q1

variable {α : Type*} [DecidableEq α]

/-- A finite sunflower, specified by equality of intersections of distinct blocks. -/
def IsSunflower (family : Finset (Finset α)) (core : Finset α) : Prop :=
  ∀ A ∈ family, ∀ B ∈ family, A ≠ B → A ∩ B = core

private theorem exists_sunflower_aux (k n : ℕ) (_hn : 1 ≤ n)
    (family : Finset (Finset α))
    (hcard : ∀ A ∈ family, A.card = k)
    (hlarge : k.factorial * n ^ k < family.card) :
    ∃ subfamily core, subfamily ⊆ family ∧ subfamily.card = n + 1 ∧
      core.card < k ∧ IsSunflower subfamily core ∧
      (∀ A ∈ subfamily, core ⊆ A) := by
  classical
  induction k generalizing family with
  | zero =>
    have hsmall : family.card ≤ 1 := Finset.card_le_one.mpr (by
      intro A hA B hB
      have ha : A = ∅ := Finset.card_eq_zero.mp (hcard A hA)
      have hb : B = ∅ := Finset.card_eq_zero.mp (hcard B hB)
      rw [ha, hb])
    simp only [Nat.factorial_zero, pow_zero, mul_one] at hlarge
    omega
  | succ k ih =>
    let D := family.powerset.filter (fun M => IsSunflower M ∅)
    have hD : D.Nonempty := by
      refine ⟨∅, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_powerset.mpr (Finset.empty_subset family), ?_⟩
      intro A hA
      exact (Finset.notMem_empty A hA).elim
    obtain ⟨M, hMD, hmax⟩ := Finset.exists_max_image D Finset.card hD
    have hMsub : M ⊆ family :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hMD).1
    have hMflower : IsSunflower M ∅ := (Finset.mem_filter.mp hMD).2
    by_cases hmany : n + 1 ≤ M.card
    · obtain ⟨L, hLM, hLcard⟩ := Finset.exists_subset_card_eq hmany
      refine ⟨L, ∅, hLM.trans hMsub, hLcard, by simp, ?_, ?_⟩
      · intro A hA B hB hAB
        exact hMflower A (hLM hA) B (hLM hB) hAB
      · intro A hA
        exact Finset.empty_subset A
    · have hMsmall : M.card ≤ n := by omega
      let U : Finset α := M.biUnion id
      have hcover : ∀ A ∈ family, ∃ u ∈ U, u ∈ A := by
        intro A hA
        by_contra hmiss
        have hd : ∀ B ∈ M, A ∩ B = ∅ := by
          intro B hB
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro u hu
          obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
          exact hmiss ⟨u, Finset.mem_biUnion.mpr ⟨B, hB, huB⟩, huA⟩
        have hAnot : A ∉ M := by
          intro hAM
          have he : A = ∅ := by simpa using hd A hAM
          have hc := hcard A hA
          simp [he] at hc
        have hins : insert A M ∈ D := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
          · exact Finset.insert_subset_iff.mpr ⟨hA, hMsub⟩
          · intro B hB C hC hBC
            rcases Finset.mem_insert.mp hB with hBA | hBM
            · rcases Finset.mem_insert.mp hC with hCA | hCM
              · exact (hBC (hBA.trans hCA.symm)).elim
              · rw [hBA]
                exact hd C hCM
            · rcases Finset.mem_insert.mp hC with hCA | hCM
              · rw [hCA, Finset.inter_comm]
                exact hd B hBM
              · exact hMflower B hBM C hCM hBC
        have hcmax := hmax (insert A M) hins
        rw [Finset.card_insert_of_notMem hAnot] at hcmax
        omega
      have hUcard : U.card ≤ n * (k + 1) := by
        calc
          U.card ≤ M.card * (k + 1) :=
            Finset.card_biUnion_le_card_mul M id (k + 1)
              (fun A hA => (hcard A (hMsub hA)).le)
          _ ≤ n * (k + 1) := Nat.mul_le_mul_right _ hMsmall
      have hpopular : ∃ u ∈ U,
          k.factorial * n ^ k < (family.filter (fun A => u ∈ A)).card := by
        by_contra! hnone
        have hfcover : family ⊆ U.biUnion (fun u => family.filter (fun A => u ∈ A)) := by
          intro A hA
          obtain ⟨u, huU, huA⟩ := hcover A hA
          exact Finset.mem_biUnion.mpr ⟨u, huU, Finset.mem_filter.mpr ⟨hA, huA⟩⟩
        have hbound : family.card ≤ (k + 1).factorial * n ^ (k + 1) := by
          calc
            family.card ≤ (U.biUnion (fun u => family.filter (fun A => u ∈ A))).card :=
              Finset.card_le_card hfcover
            _ ≤ U.card * (k.factorial * n ^ k) :=
              Finset.card_biUnion_le_card_mul U _ _ hnone
            _ ≤ (n * (k + 1)) * (k.factorial * n ^ k) :=
              Nat.mul_le_mul_right _ hUcard
            _ = (k + 1).factorial * n ^ (k + 1) := by
              rw [Nat.factorial_succ, pow_succ]
              ring
        omega
      obtain ⟨u, huU, hu⟩ := hpopular
      let H := family.filter (fun A => u ∈ A)
      let E := H.image (fun A => A.erase u)
      have hHmem : ∀ A ∈ H, u ∈ A := fun A hA => (Finset.mem_filter.mp hA).2
      have heraseinj : Set.InjOn (fun A : Finset α => A.erase u) H := by
        intro A hA B hB he
        have hh := congrArg (fun T : Finset α => insert u T) he
        simpa [Finset.insert_erase (hHmem A hA), Finset.insert_erase (hHmem B hB)] using hh
      have hEcard : E.card = H.card := Finset.card_image_of_injOn heraseinj
      have hEuniform : ∀ A ∈ E, A.card = k := by
        intro A hA
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
        rw [Finset.card_erase_of_mem (hHmem B hB),
          hcard B (Finset.mem_filter.mp hB).1]
        omega
      have hElarge : k.factorial * n ^ k < E.card := by
        rw [hEcard]
        exact hu
      obtain ⟨L, C, hLE, hLcard, hCcard, hflower, hcore⟩ :=
        ih E hEuniform hElarge
      have hnotu : ∀ A ∈ L, u ∉ A := by
        intro A hA
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp (hLE hA)
        exact Finset.notMem_erase u B
      have hinj : Set.InjOn (fun T : Finset α => insert u T) L := by
        intro A hA B hB he
        have hh := congrArg (fun T : Finset α => T.erase u) he
        simpa [hnotu A hA, hnotu B hB] using hh
      refine ⟨L.image (fun T => insert u T), insert u C, ?_, ?_, ?_, ?_, ?_⟩
      · intro A hA
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨D, hD, he⟩ := Finset.mem_image.mp (hLE hB)
        rw [← he, Finset.insert_erase (hHmem D hD)]
        exact (Finset.mem_filter.mp hD).1
      · rw [Finset.card_image_of_injOn hinj, hLcard]
      · have hi := Finset.card_insert_le u C
        omega
      · intro A hA B hB hAB
        obtain ⟨A', hA', rfl⟩ := Finset.mem_image.mp hA
        obtain ⟨B', hB', rfl⟩ := Finset.mem_image.mp hB
        have hne : A' ≠ B' := fun he => hAB (congrArg (fun T : Finset α => insert u T) he)
        have hh := hflower A' hA' B' hB' hne
        calc
          insert u A' ∩ insert u B' = insert u (A' ∩ B') := by
            ext x
            simp only [Finset.mem_inter, Finset.mem_insert]
            tauto
          _ = insert u C := congrArg (fun T : Finset α => insert u T) hh
      · intro A hA
        obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (hcore B hB hx)

/-- The elementary finite sunflower bound, with the strict core-size bound explicit. -/
theorem exists_sunflower (k n : ℕ) (_hk : 1 ≤ k) (hn : 1 ≤ n)
    (family : Finset (Finset α))
    (hcard : ∀ A ∈ family, A.card = k)
    (hlarge : k.factorial * n ^ k < family.card) :
    ∃ subfamily core, subfamily ⊆ family ∧ subfamily.card = n + 1 ∧
      core.card < k ∧ IsSunflower subfamily core ∧
      (∀ A ∈ subfamily, core ⊆ A) :=
  exists_sunflower_aux k n hn family hcard hlarge

/-- More sunflower blocks than forbidden points ensure an avoiding block,
provided the common core avoids the forbidden set. -/
theorem exists_disjoint_of_sunflower
    (family : Finset (Finset α)) (core F : Finset α)
    (hflower : IsSunflower family core)
    (hsize : F.card < family.card) (hdisj : Disjoint core F) :
    ∃ A ∈ family, Disjoint A F := by
  classical
  by_contra! hbad
  have hmeet : ∀ A ∈ family, ∃ x, x ∈ A ∧ x ∈ F := by
    intro A hA
    simpa [Finset.disjoint_left] using hbad A hA
  choose f hf using hmeet
  let g : family → F := fun A => ⟨f A.1 A.2, (hf A.1 A.2).2⟩
  have hginj : Function.Injective g := by
    intro A B he
    apply Subtype.ext
    by_contra hne
    have hval : f A.1 A.2 = f B.1 B.2 := congrArg Subtype.val he
    have hc : f A.1 A.2 ∈ core := by
      rw [← hflower A.1 A.2 B.1 B.2 hne]
      exact Finset.mem_inter.mpr ⟨(hf A.1 A.2).1, hval.symm ▸ (hf B.1 B.2).1⟩
    exact Finset.disjoint_left.mp hdisj hc (hf A.1 A.2).2
  have hle : family.card ≤ F.card := Finset.card_le_card_of_injective hginj
  omega

end Q1
