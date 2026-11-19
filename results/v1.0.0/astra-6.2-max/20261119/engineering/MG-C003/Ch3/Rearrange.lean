import Ch3.RealTools

namespace MG.Rearrange
open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
def S : Finset Line := {pt 0,pt 1,pt 2,pt 3}
def U : Set Line := {pt 0,pt 1,pt 2,pt 3}
theorem carrier : (S : Set Line) = U := by simp [S,U]
theorem size : S.card = 4 := by norm_num [S,pt]

open scoped Classical in
def f : Op (none : Line) := ⟨fun x => if x ∈ U then x else none,by simp⟩
def g : Op (none : Line) := ⟨fun x => if x = pt 0 then pt 0 else if x = pt 1 then pt 3 else
  if x = pt 2 then pt 1 else if x = pt 3 then pt 2 else none,by simp [pt]⟩

theorem outside {x : Line} (hx : x ∉ U) : f.func x = none ∧ g.func x = none := by
  simp only [U,mem_insert_iff,mem_singleton_iff,not_or] at hx
  exact ⟨if_neg (by simpa [U] using hx),by simp [g,hx.1,hx.2.1,hx.2.2.1,hx.2.2.2]⟩
theorem f_on {x : Line} (hx : x ∈ U) : f.func x = x := if_pos hx

theorem domain : dom f = U ∧ dom g = U := by
  constructor <;> ext x <;> by_cases hx : x ∈ U
  · have h : x ≠ none := by rcases hx with h|h|h|h <;> rw [h] <;> exact Option.some_ne_none _
    simp [dom,f_on hx,h,hx]
  · simp [dom,(outside hx).1,hx]
  · rcases hx with h|h|h|h <;> rw [h] <;> norm_num [dom,g,U,pt] <;> exact Option.some_ne_none _
  · simp [dom,(outside hx).2,hx]

theorem imageF : f.func '' U = U := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    rwa [f_on hz]
  · exact fun hx => ⟨_,hx,f_on hx⟩

theorem imageG : g.func '' U = U := by
  ext x
  norm_num [g,U,image_insert_eq,image_singleton,pt,or_comm,or_left_comm,or_assoc,eq_comm]

theorem countSmall {e : ENNReal} (he : 0 < e) (h1 : e ≤ 1) : cover usual e U = 4 := by
  rw [← carrier,fullSeparated S (readMetric id) he,size]
  · norm_num
  intro x hx y hy hd
  have h := hd.trans_le h1
  have hx' : x ∈ U := carrier ▸ hx
  have hy' : y ∈ U := carrier ▸ hy
  rcases hx' with h₁|h₁|h₁|h₁ <;> rcases hy' with h₂|h₂|h₂|h₂ <;> rw [h₁,h₂] at h ⊢ <;> norm_num [usual] at *

theorem countMiddle {e : ENNReal} (h1 : 1 < e) (h2 : e ≤ 2) : cover usual e U = 2 := by
  classical
  have hp := zero_lt_one.trans h1
  apply le_antisymm
  · let C : Finset Line := {pt 1,pt 2}
    have hn : Net usual e U C := by
      constructor
      · simp [C,U,Set.subset_def]
      · norm_num [U,C,usual,Finset.mem_insert,Finset.mem_singleton,h1,hp]
    exact (netUpper hn).trans (by norm_num [C,pt])
  · have h0 : pt 0 ∈ U := Or.inl rfl
    have h3 : pt 3 ∈ U := by simp [U]
    apply twoLower ⟨_,h0⟩
    intro c hc
    rcases hc with h|h|h|h <;> rw [h]
    · exact ⟨_,h3,h2.trans (by norm_num [usual])⟩
    · exact ⟨_,h3,h2.trans (by norm_num [usual])⟩
    · exact ⟨_,h0,h2.trans (by norm_num [usual])⟩
    · exact ⟨_,h0,h2.trans (by norm_num [usual])⟩

theorem countLarge {e : ENNReal} (he : 2 < e) : cover usual e U = 1 := by
  have h1 : pt 1 ∈ U := by simp [U]
  apply coverOne ⟨_,h1⟩ h1
  intro x hx
  apply lt_of_le_of_lt _ he
  rcases hx with h|h|h|h <;> rw [h] <;> norm_num [usual]

theorem counts {e : ENNReal} (he : positiveFinite e) :
    cover usual e U = if e ≤ 1 then 4 else if e ≤ 2 then 2 else 1 := by
  split_ifs with h k
  · exact countSmall he.1 h
  · exact countMiddle (lt_of_not_ge h) k
  · exact countLarge (lt_of_not_ge k)

theorem midpoint :
    pt (3/2) ∉ U ∧ U ⊆ ball usual (pt (3/2)) (7/4) ∧
      ∀ C : Finset Line, Net usual (7/4) U C → pt (3/2) ∉ C := by
  have hn : pt (3/2) ∉ U := by norm_num [U,pt]
  refine ⟨hn,?_,fun _ h hx => hn (h.1 hx)⟩
  intro x hx
  rcases hx with h|h|h|h <;> rw [h] <;>
    simp only [ball,mem_setOf_eq,usual,read_points,id_eq] <;>
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).1 <;>
    norm_num [ENNReal.toReal_div,ENNReal.toReal_ofReal (abs_nonneg _)]

theorem sameCounts {e : ENNReal} (he : positiveFinite e) :
    cover usual e (f.func '' U) = cover usual e U ∧ cover usual e (g.func '' U) = cover usual e U ∧
    (∃ hf : good usual usual f U e, delta usual usual f U e hf = 0) ∧
    (∃ hg : good usual usual g U e, delta usual usual g U e hg = 0) := by
  have hfin : U.Finite := carrier ▸ S.finite_toSet
  have hn := finiteCover (readMetric id) hfin he.1
  have hu : U.Nonempty := ⟨_,Or.inl rfl⟩
  obtain ⟨v,hv⟩ := finiteLog hu hn
  exact ⟨congrArg _ imageF,congrArg _ imageG,⟨Or.inl hn,by rw [delta,imageF,hv,← EReal.coe_sub]; simp⟩,
    ⟨Or.inl hn,by rw [delta,imageG,hv,← EReal.coe_sub]; simp⟩⟩

def scalar (F : Op (none : Line)) (L : ENNReal) := HasScalarLipBound (fun _ : Unit => usual) F U () () L

theorem optimalF : IsLeast {L | scalar f L} 1 := by
  constructor
  · refine ⟨domain.1.ge,fun x hx y hy => ?_⟩
    simp [f_on hx,f_on hy]
  · intro L h
    have h0 : pt 0 ∈ U := Or.inl rfl
    have h1 : pt 1 ∈ U := by simp [U]
    simpa [f_on h0,f_on h1,usual] using h.2 _ h0 _ h1

theorem optimalG : IsLeast {L | scalar g L} 3 := by
  constructor
  · refine ⟨domain.2.ge,?_⟩
    norm_num [U,g,usual,pt,readDist,extend,edist_dist,Real.dist_eq]
  · intro L h
    have h0 : pt 0 ∈ U := Or.inl rfl
    have h1 : pt 1 ∈ U := by simp [U]
    simpa [g,usual,pt,readDist,extend,edist_dist,Real.dist_eq] using h.2 _ h0 _ h1

theorem numericalBounds :
    (cover usual (7/4) (f.func '' U) ≤ cover usual ((7/4)/1) U) ∧
    (cover usual (7/4) (g.func '' U) ≤ cover usual ((7/4)/3) U) ∧
    cover usual (7/4) (f.func '' U) = 2 ∧ cover usual ((7/4)/1) U = 2 ∧
    cover usual (7/4) (g.func '' U) = 2 ∧ cover usual ((7/4)/3) U = 4 := by
  have hf := lipCover (e := 7/4) (p := usual) (q := usual) (f := f) (L := 1)
    (by constructor <;> norm_num) optimalF.1.2
  have hg := lipCover (e := 7/4) (p := usual) (q := usual) (f := g) (L := 3)
    (by constructor <;> norm_num) optimalG.1.2
  have lo : (1:ENNReal) < 7/4 := by
    apply (ENNReal.toReal_lt_toReal (by finiteness) (by finiteness)).1
    norm_num [ENNReal.toReal_div]
  have hi : (7/4:ENNReal) ≤ 2 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1
    norm_num [ENNReal.toReal_div]
  have small : ((7/4)/3:ENNReal) ≤ 1 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1
    norm_num [ENNReal.toReal_div]
  refine ⟨hf,hg,?_,?_,?_,?_⟩
  · rw [imageF,countMiddle lo hi]
  · simpa using countMiddle lo hi
  · rw [imageG,countMiddle lo hi]
  · exact countSmall (by norm_num [ENNReal.div_pos_iff]) small

end
end MG.Rearrange
