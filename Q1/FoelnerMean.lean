import Q1.FoelnerGrowth
import Mathlib.MeasureTheory.Group.FoelnerFilter
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Prod

open MeasureTheory Filter Set
open scoped ENNReal Pointwise symmDiff Topology

namespace Q1

variable {G : Type*} [Group G]

/-- A left-invariant finitely additive probability on all subsets of the group. -/
def HasInvariantMean (G : Type*) [Group G] : Prop :=
  ∃ m : Set G → ℝ≥0∞, m ∅ = 0 ∧ m Set.univ = 1 ∧
    (∀ A, m A ≤ 1) ∧
    (∀ A B, Disjoint A B → m (A ∪ B) = m A + m B) ∧
    ∀ (g : G) (A : Set G), m (g • A) = m A

noncomputable def translateSymmDiff (g : G) (F : Finset G) : Finset G := by
  classical
  exact leftTranslate g F ∆ F

/-- Equal translation cardinalities turn the one-sided loss into half the
symmetric-difference cardinality. -/
theorem leftTranslate_symmDiff_card (g : G) (F : Finset G) :
    (translateSymmDiff g F).card = 2 * (translateBoundary g F).card := by
  classical
  unfold translateSymmDiff
  have hcard : (leftTranslate g F).card = F.card := by
    exact Finset.card_image_of_injective F (mul_right_injective g)
  have he : (F \ leftTranslate g F).card =
      (leftTranslate g F \ F).card :=
    (Finset.card_sdiff_eq_card_sdiff_iff).mpr hcard.symm
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  · rw [he]
    change _ = 2 * (leftTranslate g F \ F).card
    omega
  · exact disjoint_sdiff_sdiff

theorem coe_leftTranslate (g : G) (F : Finset G) :
    (leftTranslate g F : Set G) = g • (F : Set G) := by
  classical
  ext x
  simp only [leftTranslate, Finset.mem_coe, Finset.mem_image, Set.mem_smul_set, smul_eq_mul]

/-- The explicit finite Følner condition yields an invariant probability on
every subset, with no Følner-filter hypothesis left to the caller. -/
theorem hasInvariantMean_of_finiteFoelner (h : FiniteFoelner G) :
    HasInvariantMean G := by
  classical
  let : MeasurableSpace G := ⊤
  let I := Finset G × ℕ
  have hex (i : I) : ∃ F : Finset G, F.Nonempty ∧
      ∀ g ∈ i.1, ((translateBoundary g F).card : ℝ) ≤
        (1 / ((i.2 : ℝ) + 1)) * F.card :=
    h i.1 (1 / ((i.2 : ℝ) + 1)) (by positivity)
  choose F hF hbd using hex
  have hpos (i : I) : (0 : ℝ) < (F i).card := by
    exact_mod_cast Finset.card_pos.mpr (hF i)
  have hsnd : Tendsto (fun i : I => i.2) atTop atTop := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact tendsto_snd
  have ht : Tendsto (fun i : I => (2 : ℝ) * (1 / ((i.2 : ℝ) + 1)))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hsnd))
  have hratio (g : G) :
      Tendsto (fun i : I =>
        ((leftTranslate g (F i) ∆ F i).card : ℝ) / (F i).card) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun i => by positivity)) ?_ ht
    filter_upwards [eventually_ge_atTop (({g} : Finset G), 0)] with i hi
    have hg : g ∈ i.1 := hi.1 (by simp)
    have hb := hbd i g hg
    have hc : ((leftTranslate g (F i) ∆ F i).card : ℝ) =
        2 * (translateBoundary g (F i)).card := by
      exact_mod_cast leftTranslate_symmDiff_card g (F i)
    apply (div_le_iff₀ (hpos i)).mpr
    rw [hc]
    nlinarith
  have hfoel : IsFoelner G (Measure.count : Measure G)
      (atTop : Filter I) (fun i => (F i : Set G)) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Eventually.of_forall (fun _ => MeasurableSet.of_discrete)
    · apply Eventually.of_forall
      intro i
      rw [Measure.count_apply_finset]
      exact_mod_cast (Finset.card_pos.mpr (hF i)).ne'
    · apply Eventually.of_forall
      intro i
      rw [Measure.count_apply_finset]
      exact ENNReal.natCast_ne_top _
    · intro g
      have ht' := ENNReal.tendsto_ofReal (hratio g)
      simp only [ENNReal.ofReal_zero] at ht'
      convert ht' using 1
      ext i
      rw [← coe_leftTranslate, ← Finset.coe_symmDiff,
        Measure.count_apply_finset, Measure.count_apply_finset,
        ENNReal.ofReal_div_of_pos (hpos i)]
      simp
  obtain ⟨m, hm1, hmadd, hminv⟩ := hfoel.amenable
  have hadd (A B : Set G) (hd : Disjoint A B) :
      m (A ∪ B) = m A + m B := hmadd A B MeasurableSet.of_discrete hd
  have hm0 : m ∅ = 0 := by
    have he : m ∅ + 1 = 0 + 1 := by
      simpa [hm1] using (hadd ∅ Set.univ (by simp)).symm
    exact (ENNReal.add_left_inj (by norm_num : (1 : ℝ≥0∞) ≠ ∞)).mp he
  have hmle (A : Set G) : m A ≤ 1 := by
    have he := hadd A Aᶜ disjoint_compl_right
    rw [Set.union_compl_self, hm1] at he
    calc
      m A ≤ m A + m Aᶜ := le_add_right le_rfl
      _ = 1 := he.symm
  exact ⟨m, hm0, hm1, hmle, hadd, hminv⟩

end Q1
