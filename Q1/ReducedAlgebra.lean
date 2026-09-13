import Q1.RegularRepresentation
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Topology.Algebra.StarSubalgebra

/-! The reduced group C*-algebra is the operator-norm closure of the finite
complex linear span of the left translations on the full `GroupL2 G`. -/

noncomputable section
open scoped InnerProduct
namespace Q1
variable {G : Type*} [Group G]

abbrev RegularOperator (G : Type*) := GroupL2 G →L[ℂ] GroupL2 G

@[simp] theorem leftRegular_one_eq_one : leftRegular (1 : G) = 1 := leftRegular_one

theorem leftRegular_mul_eq_mul (g h : G) :
    leftRegular (g * h) = leftRegular g * leftRegular h := leftRegular_mul g h

@[simp] theorem star_leftRegular (g : G) : star (leftRegular g) = leftRegular g⁻¹ := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro x y
  have h := (leftRegularIsometry g).inner_map_map (leftRegular g⁻¹ x) y
  have hx : leftRegular g (leftRegular g⁻¹ x) = x := by
    rw [← ContinuousLinearMap.comp_apply, ← leftRegular_mul]
    simp
  change inner ℂ (leftRegular g (leftRegular g⁻¹ x)) (leftRegular g y) = _ at h
  rw [hx] at h
  exact h.symm

/-- The finite complex span of the actual left translations. -/
def finiteRegularSpan : Submodule ℂ (RegularOperator G) :=
  Submodule.span ℂ (Set.range (leftRegular (G := G)))

theorem leftRegular_mem_finiteRegularSpan (g : G) : leftRegular g ∈ finiteRegularSpan :=
  Submodule.subset_span ⟨g, rfl⟩

theorem regularConvolution_mem_finiteRegularSpan (f : G →₀ ℂ) :
    regularConvolution f ∈ finiteRegularSpan := by
  classical
  exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (leftRegular_mem_finiteRegularSpan g)

theorem mem_finiteRegularSpan_iff (a : RegularOperator G) :
    a ∈ finiteRegularSpan ↔ ∃ f : G →₀ ℂ, regularConvolution f = a := by
  classical
  constructor
  · intro ha
    induction ha using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact ⟨Finsupp.single g 1, by simp⟩
    | zero => exact ⟨0, regularConvolution_zero⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, rfl⟩ := hx
      obtain ⟨h, rfl⟩ := hy
      exact ⟨f + h, regularConvolution_add f h⟩
    | smul c x _ hx =>
      obtain ⟨f, rfl⟩ := hx
      exact ⟨c • f, regularConvolution_smul c f⟩
  · rintro ⟨f, rfl⟩
    exact regularConvolution_mem_finiteRegularSpan f

theorem mul_mem_finiteRegularSpan {a b : RegularOperator G}
    (ha : a ∈ finiteRegularSpan) (hb : b ∈ finiteRegularSpan) :
    a * b ∈ finiteRegularSpan := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨h, rfl⟩ := hb
      rw [← leftRegular_mul_eq_mul]
      exact leftRegular_mem_finiteRegularSpan _
    | zero => simp
    | add x y _ _ hx hy => simpa [mul_add] using (finiteRegularSpan.add_mem hx hy)
    | smul c x _ hx => simpa [mul_smul_comm] using (finiteRegularSpan.smul_mem c hx)
  | zero => simp
  | add x y _ _ hx hy => simpa [add_mul] using (finiteRegularSpan.add_mem hx hy)
  | smul c x _ hx => simpa [smul_mul_assoc] using (finiteRegularSpan.smul_mem c hx)

theorem star_mem_finiteRegularSpan {a : RegularOperator G} (ha : a ∈ finiteRegularSpan) :
    star a ∈ finiteRegularSpan := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    simpa using leftRegular_mem_finiteRegularSpan g⁻¹
  | zero => simp
  | add x y _ _ hx hy => simpa using (finiteRegularSpan.add_mem hx hy)
  | smul c x _ hx => simpa using (finiteRegularSpan.smul_mem (star c) hx)

/-- The finite group algebra represented faithfully by left convolution. -/
def finiteRegularAlgebra : StarSubalgebra ℂ (RegularOperator G) where
  carrier := (finiteRegularSpan (G := G) : Set (RegularOperator G))
  zero_mem' := finiteRegularSpan.zero_mem
  add_mem' := finiteRegularSpan.add_mem
  mul_mem' := mul_mem_finiteRegularSpan
  one_mem' := by
    change (1 : RegularOperator G) ∈ finiteRegularSpan
    rw [← leftRegular_one_eq_one]
    exact leftRegular_mem_finiteRegularSpan 1
  algebraMap_mem' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    apply finiteRegularSpan.smul_mem
    rw [← leftRegular_one_eq_one]
    exact leftRegular_mem_finiteRegularSpan 1
  star_mem' := star_mem_finiteRegularSpan

/-- The concrete reduced group C*-algebra as a closed star subalgebra of `B(ℓ²(G))`. -/
def reducedGroupAlgebra : StarSubalgebra ℂ (RegularOperator G) :=
  finiteRegularAlgebra.topologicalClosure

/-- The elements of the concrete reduced group C*-algebra, with inherited operator norm. -/
abbrev ReducedGroupCStarAlgebra (G : Type*) [Group G] := reducedGroupAlgebra (G := G)

instance : CompleteSpace (ReducedGroupCStarAlgebra G) :=
  inferInstanceAs (CompleteSpace (finiteRegularAlgebra (G := G)).topologicalClosure)

instance reducedGroupAlgebra_isClosed :
    IsClosed (reducedGroupAlgebra (G := G) : Set (RegularOperator G)) :=
  finiteRegularAlgebra.isClosed_topologicalClosure

instance : CStarAlgebra (ReducedGroupCStarAlgebra G) :=
  StarSubalgebra.cstarAlgebra _

theorem mem_reducedGroupAlgebra_iff (a : RegularOperator G) :
    a ∈ reducedGroupAlgebra ↔ a ∈ closure (Set.range (regularConvolution (G := G))) := by
  change a ∈ closure (finiteRegularAlgebra (G := G) : Set _) ↔ _
  have hs : (finiteRegularAlgebra (G := G) : Set (RegularOperator G)) =
      Set.range (regularConvolution (G := G)) := by
    ext b
    exact mem_finiteRegularSpan_iff b
  rw [hs]

theorem regularConvolution_mem_reducedGroupAlgebra (f : G →₀ ℂ) :
    regularConvolution f ∈ reducedGroupAlgebra :=
  finiteRegularAlgebra.le_topologicalClosure (show regularConvolution f ∈ finiteRegularAlgebra from
    regularConvolution_mem_finiteRegularSpan f)

/-- The finite coefficient operator, viewed inside the norm-completed reduced algebra. -/
def reducedPolynomial (f : G →₀ ℂ) : ReducedGroupCStarAlgebra G :=
  ⟨regularConvolution f, regularConvolution_mem_reducedGroupAlgebra f⟩

@[simp] theorem reducedPolynomial_coe (f : G →₀ ℂ) :
    (reducedPolynomial f : RegularOperator G) = regularConvolution f := rfl

@[simp] theorem norm_reducedPolynomial (f : G →₀ ℂ) :
    ‖reducedPolynomial f‖ = ‖regularConvolution f‖ := rfl

/-- Density is in the full operator norm, with no finite-dimensional truncation. -/
theorem exists_reducedPolynomial_near (a : ReducedGroupCStarAlgebra G) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : G →₀ ℂ, ‖reducedPolynomial f - a‖ < ε := by
  have ha := (mem_reducedGroupAlgebra_iff (a : RegularOperator G)).mp a.property
  obtain ⟨b, ⟨f, rfl⟩, hf⟩ := Metric.mem_closure_iff.mp ha ε hε
  exact ⟨f, by simpa [dist_eq_norm, norm_sub_rev] using hf⟩

/-- The actual left regular representation as a monoid homomorphism. -/
def regularRepresentation : G →* RegularOperator G where
  toFun := leftRegular
  map_one' := leftRegular_one_eq_one
  map_mul' := leftRegular_mul_eq_mul

@[simp] theorem regularRepresentation_apply (g : G) :
    regularRepresentation g = leftRegular g := rfl

/-- The same unitary translations inside the reduced group algebra. -/
def reducedLeftRegular : G →* ReducedGroupCStarAlgebra G where
  toFun g := ⟨leftRegular g, finiteRegularAlgebra.le_topologicalClosure
    (leftRegular_mem_finiteRegularSpan g)⟩
  map_one' := Subtype.ext leftRegular_one_eq_one
  map_mul' g h := Subtype.ext (leftRegular_mul_eq_mul g h)

@[simp] theorem reducedLeftRegular_coe (g : G) :
    (reducedLeftRegular g : RegularOperator G) = leftRegular g := rfl

@[simp] theorem norm_reducedLeftRegular (g : G) : ‖reducedLeftRegular g‖ = 1 :=
  norm_leftRegular g

/-- The reduced algebra is nonzero, since the identity translation has norm one. -/
instance : Nontrivial (ReducedGroupCStarAlgebra G) := by
  refine ⟨⟨0, reducedLeftRegular (1 : G), ?_⟩⟩
  intro h
  have he := congrArg norm h
  simp only [norm_zero, norm_reducedLeftRegular, zero_ne_one] at he

end Q1
