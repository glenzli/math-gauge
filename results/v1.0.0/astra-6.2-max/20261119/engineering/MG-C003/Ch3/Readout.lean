import Ch3.RealTools

namespace MG
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
open scoped Classical in
theorem fiberInsert {X : Type} {b : X} (p : Dist X) (f : Op b) (x : X) (S : Set X) (y : X) :
    fiber p f (insert x S) y = if p (f.func x) y = 0 then insert x (fiber p f S y) else fiber p f S y := by
  ext a
  by_cases h : p (f.func x) y = 0 <;> by_cases ha : a = x <;> simp [fiber,h,ha]
open scoped Classical in
theorem fiberSingle {X : Type} {b : X} (p : Dist X) (f : Op b) (x y : X) :
    fiber p f {x} y = if p (f.func x) y = 0 then {x} else ∅ := by
  ext a
  by_cases h : p (f.func x) y = 0 <;> by_cases ha : a = x <;> simp [fiber,h,ha]

namespace Affine
def U : Set Line := {pt 0,pt 1}
def f := liftOp fun x : ℝ => 2*x-1
theorem domain : U ⊆ dom f ∧ U ⊆ dom (f*f) := by
  constructor <;> intro x hx <;> rcases hx with h|h <;> rw [h] <;> exact Option.some_ne_none _

theorem firstStep : fiber absolute f U (f.func (pt 0)) = U ∧ Const absolute f U := by
  constructor
  · norm_num [U,f,absolute,fiberInsert,fiberSingle]
  · intro x hx y hy
    rcases hx with h|h <;> rcases hy with k|k <;> rw [h,k] <;> norm_num [f,absolute]

theorem secondStep : fiber absolute (f*f) U ((f*f).func (pt 0)) = {pt 0} ∧ Active absolute (f*f) U := by
  have h0 : pt 0 ∈ U := Or.inl rfl
  have h1 : pt 1 ∈ U := Or.inr rfl
  refine ⟨?_,fun hc => ?_,fun hi => ?_⟩
  · norm_num [U,f,absolute,fiberInsert,fiberSingle]
  · have h := hc _ h0 _ h1
    norm_num [f,absolute] at h
  · have h := hi.2 _ h0
    norm_num [f,absolute] at h

theorem sameValue (g : Op (none : Line)) (c : ℝ) (h : ∀ x ∈ U, g.func x = pt c) :
    (∀ x ∈ U, (g*g).func x = g.func (pt c)) ∧
    (∀ y, pt 0 ∈ fiber absolute (g*g) U y ↔ pt 1 ∈ fiber absolute (g*g) U y) ∧
    (U ⊆ dom (g*g) ↔ g.func (pt c) ≠ none) ∧
    (g.func (pt c) = none → Disjoint U (dom (g*g))) := by
  have H : ∀ x ∈ U, (g*g).func x = g.func (pt c) := fun x hx => congrArg g.func (h x hx)
  have h0 : pt 0 ∈ U := Or.inl rfl
  have h1 : pt 1 ∈ U := Or.inr rfl
  refine ⟨H,fun y => ?_,⟨fun hd => ?_,fun hn x hx => ?_⟩,fun hn => ?_⟩
  · simp only [fiber,mem_setOf_eq,h0,h1,H _ h0,H _ h1]
  · simpa only [dom,mem_setOf_eq,H _ h0] using hd h0
  · exact fun hb => hn ((H _ hx).symm.trans hb)
  · exact Set.disjoint_left.2 fun x hx hd => hd ((H _ hx).trans hn)
end Affine

namespace Translation
def U : Set Line := {pt (-3),pt (-2),pt 0,pt 2}
def f := liftOp fun x : ℝ => x+1
theorem domain : U ⊆ dom f ∧ U ⊆ dom (1 : Op (none : Line)) := by
  constructor <;> intro x hx <;> rcases hx with h|h|h|h <;> rw [h] <;> exact Option.some_ne_none _

theorem translated : f.func '' U = {pt (-2),pt (-1),pt 1,pt 3} := by
  norm_num [U,f,image_insert_eq,image_singleton]

theorem partitionId : blocks absolute (1 : Op (none : Line)) U =
    {{pt (-3)}, {pt (-2),pt 2}, {pt 0}} := by
  norm_num [blocks,U,image_insert_eq,image_singleton,fiberInsert,fiberSingle,absolute,Set.insert_comm,Set.pair_comm]

theorem partitionShift : blocks absolute f U =
    {{pt (-3)}, {pt (-2),pt 0}, {pt 2}} := by
  norm_num [blocks,U,image_insert_eq,image_singleton,fiberInsert,fiberSingle,f,absolute,Set.insert_comm,Set.pair_comm]

private theorem one_lt_eps : (1 : ENNReal) < 3/2 := by
  apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).1
  norm_num [ENNReal.toReal_div]
private theorem eps_le_two : (3/2 : ENNReal) ≤ 2 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1
  norm_num [ENNReal.toReal_div]
theorem inputCount : cover absolute (3/2) U = 2 := by
  classical
  have h0 : pt 0 ∈ U := by simp [U]
  have h2 : pt 2 ∈ U := by simp [U]
  apply le_antisymm
  · let C : Finset Line := {pt (-2),pt 0}
    have hC : Net absolute (3/2) U C := by
      constructor
      · simp [C,U,Set.subset_def]
      · norm_num [U,C,absolute,one_lt_eps,Finset.mem_insert,Finset.mem_singleton]
    exact (netUpper hC).trans (by norm_num [C,pt])
  · apply twoLower ⟨_,h0⟩
    intro c hc
    rcases hc with h|h|h|h <;> rw [h]
    · exact ⟨_,h0,by norm_num [absolute]; exact eps_le_two.trans (by norm_num)⟩
    · exact ⟨_,h0,by norm_num [absolute]; exact eps_le_two⟩
    · exact ⟨_,h2,by norm_num [absolute]; exact eps_le_two⟩
    · exact ⟨_,h0,by norm_num [absolute]; exact eps_le_two⟩

theorem outputCount : cover absolute (3/2) (f.func '' U) = 1 := by
  rw [translated]
  have h : pt (-2) ∈ ({pt (-2),pt (-1),pt 1,pt 3} : Set Line) := Or.inl rfl
  apply coverOne ⟨_,h⟩ h
  norm_num [absolute,one_lt_eps]

theorem entropyChange : ∃ h : good absolute absolute f U (3/2), delta absolute absolute f U (3/2) h = 1 := by
  refine ⟨Or.inr (outputCount.trans_lt ENNReal.one_lt_top),?_⟩
  change log2_ereal (cover absolute (3/2) U) - log2_ereal (cover absolute (3/2) (f.func '' U)) = 1
  rw [inputCount, outputCount]
  norm_num [log2_ereal, Real.logb_self_eq_one]
end Translation
end
end MG
