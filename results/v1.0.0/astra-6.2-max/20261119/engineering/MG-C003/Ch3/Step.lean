import Ch3.RealTools

namespace MG.Step
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
def W : Set ℝ := Ico (-1) 0 ∪ Ioc 0 1
def U := realSet W
def v (x : ℝ) : ℝ := if x < 0 then 0 else 1
def f := liftOp v
theorem domain : U.Nonempty ∧ U ⊆ dom f :=
  ⟨realNonempty ⟨1,Or.inr ⟨zero_lt_one,le_rfl⟩⟩,realDom v W⟩

theorem across {y R : ℝ} (hy : y ∈ W) (hR : |y| < R) :
    ∃ x ∈ W, |x-y| < R ∧ v x ≠ v y := by
  let a := min 1 ((R - |y|)/2)
  have hp : 0 < a := lt_min zero_lt_one (by linarith)
  have h1 : a ≤ 1 := min_le_left _ _
  have h2 : a ≤ (R - |y|)/2 := min_le_right _ _
  rcases hy with hy | hy
  · have hy' := hy.2
    rw [abs_of_neg hy'] at hR h2
    refine ⟨a,Or.inr ⟨hp,h1⟩,?_,by simp [v,hp.not_gt,hy']⟩
    rw [abs_of_pos (by linarith : 0 < a-y)]
    linarith
  · have hy' := hy.1
    rw [abs_of_pos hy'] at hR h2
    refine ⟨-a,Or.inl ⟨by linarith,by linarith⟩,?_,by simp [v,hp,hy'.not_gt]⟩
    rw [abs_of_neg (by linarith : -a-y < 0)]
    linarith

theorem step_eq_zero {x y : ℝ} : usual (f.func (pt x)) (f.func (pt y)) = 0 ↔ v x = v y := by
  change edist (v x) (v y) = 0 ↔ _
  exact edist_eq_zero

theorem legal_iff {y : ℝ} (hy : y ∈ W) {r : ENNReal} :
    r ∈ legal usual usual f U (pt y) ↔ 0 < r ∧ r ≤ ENNReal.ofReal |y| := by
  constructor
  · intro hr
    refine ⟨hr.1.1,le_of_not_gt ?_⟩
    intro h
    have hR := (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg y) hr.1.2.ne).1 h
    obtain ⟨x,hx,hd,hv⟩ := across hy hR
    apply hv
    apply step_eq_zero.1 (hr.2 _ (mem_realSet.2 hx) ?_)
    simpa only [usual,read_points,id_eq,ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.1.2.ne] using hd
  · rintro ⟨hp,hl⟩
    refine ⟨⟨hp,hl.trans_lt ENNReal.ofReal_lt_top⟩,?_⟩
    rintro _ ⟨x,hx,rfl⟩ hd
    have hy0 : y ≠ 0 := by rcases hy with h|h; exact h.2.ne; exact h.1.ne'
    have hxy : |x-y| < |y| :=
      (ENNReal.ofReal_lt_ofReal_iff (abs_pos.2 hy0)).1 (by simpa [usual] using hd.trans_le hl)
    apply step_eq_zero.2
    rw [abs_lt] at hxy
    by_cases hn : y < 0
    · rw [abs_of_neg hn] at hxy
      have hx' : x < 0 := by linarith
      simp [v,hn,hx']
    · rw [abs_of_nonneg (le_of_not_gt hn)] at hxy
      have hx' : 0 < x := by linarith
      simp [v,hn,hx'.not_gt]

theorem pointValue {y : ℝ} (hy : y ∈ W) :
    radius usual usual f U (pt y) = ENNReal.ofReal |y| ∧ 0 < ENNReal.ofReal |y| := by
  have hn : y ≠ 0 := by rcases hy with h|h; exact h.2.ne; exact h.1.ne'
  have hp := ENNReal.ofReal_pos.2 (abs_pos.2 hn)
  exact ⟨le_antisymm (sSup_le fun _ hr => ((legal_iff hy).1 hr).2) (le_sSup ((legal_iff hy).2 ⟨hp,le_rfl⟩)),hp⟩

theorem uniformZero : uniform usual usual f U U = 0 := by
  apply smallZero
  intro t ht
  let a := min 1 t
  have hp : 0 < a := lt_min zero_lt_one ht
  have ha : a ∈ W := Or.inr ⟨hp,min_le_left _ _⟩
  calc
    _ ≤ radius usual usual f U (pt a) := uniform_le (mem_realSet.2 ha)
    _ = ENNReal.ofReal |a| := (pointValue ha).1
    _ ≤ _ := by rw [abs_of_pos hp]; exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

theorem noUniformCover {τ : ENNReal} (ht : positiveFinite τ) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2*a) < τ ∧
      ({pt (-a),pt a} : Set Line) ⊆ U ∧
      cover usual τ {pt (-a),pt a} = 1 ∧ cover usual (1/2) (f.func '' {pt (-a),pt a}) = 2 := by
  let a := min 1 (τ.toReal/4)
  have hτ := ENNReal.toReal_pos ht.1.ne' ht.2.ne
  have ha : 0 < a := lt_min zero_lt_one (by linarith)
  have h1 : a ≤ 1 := min_le_left _ _
  have h2 : a ≤ τ.toReal/4 := min_le_right _ _
  have hτ' : ENNReal.ofReal (2*a) < τ := (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) ht.2.ne).2 (by linarith)
  refine ⟨a,ha,h1,hτ',?_,?_,?_⟩
  · intro x hx
    rcases hx with h|h <;> rw [h] <;> apply mem_realSet.2
    · exact Or.inl ⟨by linarith,by linarith⟩
    · exact Or.inr ⟨ha,h1⟩
  · rw [pairCover (readMetric id) _ _ ht.1,if_pos]
    simpa [usual,abs_of_neg (by linarith : -a-a < 0),two_mul] using hτ'
  · rw [Set.image_insert_eq,Set.image_singleton,pairCover (readMetric id) _ _ (by norm_num),if_neg]
    simp [f,v,ha,ha.not_gt]

end
end MG.Step
