import Chapter3.Models

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
noncomputable section

def componentPartition {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (f : Operator X bot) (i : I) (U : Set X) : Set (Set X) :=
  (fun x => componentFiber d f i (f.func x) U) '' U
theorem componentPartition_targets {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (f : Operator X bot) (i : I) (U : Set X) :
    componentPartition d f i U = (fun y => componentFiber d f i y U) '' (f.func '' U) := by
  simp [componentPartition,image_image]

namespace Affine
def d : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => absDistance
def f := pointedOp (fun x : ℝ => 2*x-1)
def U : Set (Option ℝ) := {some 0,some 1}
theorem legal : ExtendedPseudoMetric (Option ℝ) none (d ()) ∧ U ⊆ dom f ∧ U ⊆ dom (f*f) := by
  refine ⟨absDistance_metric,?_,?_⟩ <;>
    intro x hx <;> rcases hx with rfl | rfl <;> simp [f,dom]
theorem fibers :
    componentFiber d f () (f.func (some 0)) U = U ∧
    componentFiber d (f*f) () ((f*f).func (some 0)) U = {some 0} := by
  constructor
  · ext x
    constructor
    · exact And.left
    · intro hx
      refine ⟨hx,?_⟩
      rcases hx with rfl | rfl <;> norm_num [d,f]
  · ext x
    constructor
    · rintro ⟨hx,hd⟩
      rcases hx with rfl | rfl <;> norm_num [d,f] at *
    · intro hx
      rcases hx with rfl
      norm_num [componentFiber,U,d,f]
theorem types :
    constComponents d f U = univ ∧ idComponents d f U = ∅ ∧ actComponents d f U = ∅ ∧
    actComponents d (f*f) U = univ := by
  have hc : constComponents d f U = univ := by
    ext i; cases i
    norm_num [constComponents,U,d,f]
  refine ⟨hc,by simp [idComponents,hc],by simp [actComponents,idComponents,hc],?_⟩
  ext i; cases i
  norm_num [actComponents,idComponents,constComponents,U,d,f]

theorem same_value_square (g : Operator (Option ℝ) none) (c : ℝ)
    (h0 : g.func (some 0) = some c) (h1 : g.func (some 1) = some c) :
    (g*g).func (some 0) = (g*g).func (some 1) ∧
    absDistance ((g*g).func (some 0)) ((g*g).func (some 1)) = 0 ∧
    (U ⊆ dom (g*g) ↔ g.func (some c) ≠ none) := by
  have he : (g*g).func (some 0) = (g*g).func (some 1) := by simp [h0,h1]
  refine ⟨he,by rw [he]; exact absDistance_metric.dist_self _,?_⟩
  constructor
  · intro h
    simpa [dom,h0] using h (by simp [U] : some (0 : ℝ) ∈ U)
  · intro h x hx
    rcases hx with rfl | rfl <;> simpa [dom,h0,h1] using h
end Affine

namespace Translation
def d : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => absDistance
def f := pointedOp (fun x : ℝ => x+1)
def U : Set (Option ℝ) := {some (-3),some (-2),some 0,some 2}
def V : Set (Option ℝ) := {some (-2),some (-1),some 1,some 3}
theorem legal : ExtendedPseudoMetric (Option ℝ) none (d ()) ∧ U ⊆ dom f := by
  refine ⟨absDistance_metric,?_⟩
  intro x hx
  rcases hx with rfl | rfl | rfl | rfl <;> simp [f,dom]
theorem image : f.func '' U = V := by
  norm_num [f,U,V,image_insert_eq,image_singleton]

theorem id_fibers :
    componentFiber d (1 : Operator (Option ℝ) none) () (some (-3)) U = {some (-3)} ∧
    componentFiber d (1 : Operator (Option ℝ) none) () (some (-2)) U = {some (-2),some 2} ∧
    componentFiber d (1 : Operator (Option ℝ) none) () (some 0) U = {some 0} ∧
    componentFiber d (1 : Operator (Option ℝ) none) () (some 2) U = {some (-2),some 2} := by
  repeat' constructor
  all_goals
    ext x
    constructor
    · rintro ⟨hx,hd⟩
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num [d] at *
    · intro hx
      rcases hx with rfl | rfl <;> norm_num [componentFiber,U,d]

theorem translated_fibers :
    componentFiber d f () (f.func (some (-3))) U = {some (-3)} ∧
    componentFiber d f () (f.func (some (-2))) U = {some (-2),some 0} ∧
    componentFiber d f () (f.func (some 0)) U = {some (-2),some 0} ∧
    componentFiber d f () (f.func (some 2)) U = {some 2} := by
  repeat' constructor
  all_goals
    ext x
    constructor
    · rintro ⟨hx,hd⟩
      rcases hx with rfl | rfl | rfl | rfl <;> norm_num [d,f] at *
    · intro hx
      rcases hx with rfl | rfl <;> norm_num [componentFiber,U,d,f]

theorem partitions :
    componentPartition d (1 : Operator (Option ℝ) none) () U =
      {{some (-3)}, {some (-2),some 2}, {some 0}} ∧
    componentPartition d f () U = {{some (-3)}, {some (-2),some 0}, {some 2}} := by
  simp only [componentPartition,U,image_insert_eq,image_singleton,op_one_apply]
  rw [show ({some (-3),some (-2),some 0,some 2} : Set (Option ℝ)) = U from rfl]
  simp only [id_fibers.1,id_fibers.2.1,id_fibers.2.2.1,id_fibers.2.2.2,
    translated_fibers.1,translated_fibers.2.1,translated_fibers.2.2.1,translated_fibers.2.2.2]
  constructor <;> ext S <;> simp <;> tauto

theorem input_cover : covering_number absDistance (3/2) U = 2 := by
  classical
  apply le_antisymm
  · have hn : InternalEpsilonNet absDistance (3/2) U {some 0,some 2} := by
      norm_num [InternalEpsilonNet,U,Set.insert_subset_iff,ENNReal.lt_div_iff_mul_lt]
    simpa using cover_le_net _ _ _ _ hn
  · apply cover_two_lower _ _ _ ⟨some 0,by simp [U]⟩
    intro c hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨some 0,by simp [U],by norm_num [ENNReal.div_le_iff]⟩
    · exact ⟨some 0,by simp [U],by norm_num [ENNReal.div_le_iff]⟩
    · exact ⟨some 2,by simp [U],by norm_num [ENNReal.div_le_iff]⟩
    · exact ⟨some 0,by simp [U],by norm_num [ENNReal.div_le_iff]⟩

theorem output_cover : covering_number absDistance (3/2) (f.func '' U) = 1 := by
  classical
  rw [image]
  apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ ⟨some (-2),by simp [V]⟩)
  have hn : InternalEpsilonNet absDistance (3/2) V {some (-2)} := by
    norm_num [InternalEpsilonNet,V,Set.insert_subset_iff,ENNReal.lt_div_iff_mul_lt]
  simpa using cover_le_net _ _ _ _ hn

theorem entropy_difference :
    ∃ h : entropyDifferenceDefined absDistance absDistance f (3/2) U,
      entropyDifference absDistance absDistance f (3/2) U h = 1 := by
  have hd : entropyDifferenceDefined absDistance absDistance f (3/2) U :=
    ⟨⟨some 0,by simp [U]⟩,legal.2,ENNReal.div_pos (by norm_num) (by norm_num),
      by finiteness,Or.inr (by rw [output_cover]; norm_num)⟩
  refine ⟨hd,?_⟩
  norm_num [entropyDifference,metric_entropy,input_cover,output_cover,log2_ereal]
end Translation

end
end Chapter3
