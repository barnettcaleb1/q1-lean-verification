import Q1.FoelnerMean
import Q1.NormalClosureWitness

/-! Exact normal-amenability hypotheses, with an invariant probability on all
subsets as the amenability convention. No existence of an amenable radical is
postulated as an axiom or inferred from a name. -/

namespace Q1

variable {G : Type*} [Group G]

/-- Every normal subgroup admitting an invariant probability lies in R.
This domination property is precisely the part of radical maximality used in
conjugacy growth; R need not itself be amenable for this predicate. -/
def AmenableNormalCover (R : Subgroup G) : Prop :=
  ∀ N : Subgroup G, N.Normal → HasInvariantMean N → N ≤ R

/-- The defining properties of an amenable radical, for a supplied subgroup.
Existence is not asserted by this structure. -/
structure IsAmenableRadical (R : Subgroup G) : Prop where
  normal : R.Normal
  hasInvariantMean : HasInvariantMean R
  maximal : AmenableNormalCover R

theorem IsAmenableRadical.unique {R T : Subgroup G}
    (hR : IsAmenableRadical R) (hT : IsAmenableRadical T) : R = T := by
  exact le_antisymm (hT.maximal R hR.normal hR.hasInvariantMean)
    (hR.maximal T hT.normal hT.hasInvariantMean)

/-- Trivial radical domination is equivalent to absence of nontrivial normal
subgroups with invariant means, with the quantifiers made explicit. -/
theorem amenableNormalCover_bot_iff : AmenableNormalCover (⊥ : Subgroup G) ↔
    ∀ N : Subgroup G, N.Normal → HasInvariantMean N → N = ⊥ := by
  constructor
  · intro h N hn hm
    exact le_bot_iff.mp (h N hn hm)
  · intro h N hn hm
    exact le_of_eq (h N hn hm)

/-- Outside a subgroup dominating amenable normal subgroups, the actual normal
closure fails the finite Følner condition. This uses the proved direction from
finite Følner sets to an invariant mean, not an assumed criterion equivalence. -/
theorem not_finiteFoelner_normalClosure_of_amenableNormalCover
    (R : Subgroup G) (hR : AmenableNormalCover R) (g : G) (hg : g ∉ R) :
    ¬ FiniteFoelner (Subgroup.normalClosure ({g} : Set G)) := by
  intro hN
  have hle := hR (Subgroup.normalClosure ({g} : Set G)) inferInstance
    (hasInvariantMean_of_finiteFoelner hN)
  exact hg (hle (Subgroup.subset_normalClosure (by simp)))

/-- A supplied radical structure specializes the preceding theorem directly. -/
theorem not_finiteFoelner_normalClosure_of_outside_radical
    (R : Subgroup G) (hR : IsAmenableRadical R) (g : G) (hg : g ∉ R) :
    ¬ FiniteFoelner (Subgroup.normalClosure ({g} : Set G)) :=
  not_finiteFoelner_normalClosure_of_amenableNormalCover R hR.maximal g hg

end Q1
