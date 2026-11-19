import Ch3.RealTools

namespace MG.Floor
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
def f := liftOp fun x : ℝ => (⌊x⌋ : ℝ)
abbrev D (S : Set ℝ) := realSet S
def N (S : Set ℝ) := uniform usual usual f (D S) (D S)
def kind (S : Set ℝ) := bits (diam usual (D S)) (N S) 1 1
theorem channel_eq {S : Set ℝ} (h : S.Nonempty) :
    channel (diamScale (fun _ : Unit => usual)) (fun _ : Unit => usual) f ⟨D S,realNonempty h⟩
      1 1 ((),()) = kind S := rfl
theorem domain (S : Set ℝ) : D S ⊆ dom f := realDom _ S

theorem crosses {u v : ℝ} (hu : u < 1) (hv : 1 ≤ v) : N (Icc u v) = 0 := by
  apply smallZero
  intro t ht
  let a := min (min (1-u) (1/2)) t
  have ha : 0 < a := lt_min (lt_min (by linarith) (by norm_num)) ht
  have h1 : a ≤ 1-u := (min_le_left _ t).trans (min_le_left _ _)
  have h2 : a ≤ 1/2 := (min_le_left _ t).trans (min_le_right _ _)
  have h3 : a ≤ t := min_le_right _ _
  have hfloor : ⌊1-a⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by linarith,by linarith⟩
  have hx : pt (1-a) ∈ D (Icc u v) := mem_realSet.2 ⟨by linarith,by linarith⟩
  have hy : pt 1 ∈ D (Icc u v) := mem_realSet.2 ⟨hu.le,hv⟩
  have hp : 0 < usual (f.func (pt (1-a))) (f.func (pt 1)) := by norm_num [usual,f,hfloor]
  calc
    _ ≤ usual (pt (1-a)) (pt 1) := separation hx hy hp
    _ = ENNReal.ofReal a := by simp [usual,abs_of_pos ha]
    _ ≤ _ := ENNReal.ofReal_le_ofReal h3

theorem firstInterval :
    diam usual (D (Icc 0 (1/2))) = 1/2 ∧ N (Icc 0 (1/2)) = ⊤ ∧ kind (Icc 0 (1/2)) = (true,true) := by
  have hd := intervalDiam (u := 0) (v := 1/2) (by norm_num)
  norm_num at hd
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)] at hd
  have hc : Const usual f (D (Icc 0 (1/2))) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    have h (z : ℝ) (hz : z ∈ Icc (0:ℝ) (1/2)) : ⌊z⌋ = 0 :=
      Int.floor_eq_zero_iff.mpr ⟨hz.1,lt_of_le_of_lt hz.2 (by norm_num)⟩
    simp [f,usual,h x hx,h y hy]
  have hr := (constRadii usual hc).2
  exact ⟨by simpa only [one_div] using hd,hr,by unfold kind N; rw [hd,hr]; norm_num [bits]⟩

theorem jumpInterval :
    diam usual (D (Icc (9/10) (11/10))) = 1/5 ∧ N (Icc (9/10) (11/10)) = 0 ∧
    kind (Icc (9/10) (11/10)) = (true,false) := by
  have hd := intervalDiam (u := 9/10) (v := 11/10) (by norm_num)
  norm_num at hd
  norm_num [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 5)] at hd
  have hr := crosses (u := 9/10) (v := 11/10) (by norm_num) (by norm_num)
  exact ⟨by simpa only [one_div] using hd,hr,by unfold kind; rw [hd,hr]; norm_num [bits]⟩

theorem pairValue : N {0,2} = 2 := by
  apply le_antisymm
  · have hx : pt 0 ∈ D {0,2} := mem_realSet.mpr (Or.inl rfl)
    have hy : pt 2 ∈ D {0,2} := mem_realSet.mpr (Or.inr rfl)
    have h := separation (p := usual) hx hy (q := usual) (f := f) (by norm_num [f,usual])
    simpa [usual] using h
  · apply uniformBound.2
    rintro _ ⟨y,hy,rfl⟩ _ ⟨x,hx,rfl⟩
    change x = 0 ∨ x = 2 at hx
    change y = 0 ∨ y = 2 at hy
    rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> norm_num [usual,f]

theorem pairType :
    diam usual (D {0,2}) = 2 ∧ N {0,2} = 2 ∧ kind {0,2} = (false,true) := by
  have hd := pairDiam (u := 0) (v := 2) (by norm_num)
  norm_num at hd
  exact ⟨hd,pairValue,by unfold kind; rw [hd,pairValue]; norm_num [bits]⟩

theorem wholeInterval :
    diam usual (D (Icc 0 2)) = 2 ∧ N (Icc 0 2) = 0 ∧ kind (Icc 0 2) = (false,false) := by
  have hd := intervalDiam (u := 0) (v := 2) (by norm_num)
  norm_num at hd
  have hr := crosses (u := 0) (v := 2) (by norm_num) (by norm_num)
  exact ⟨by simpa only [one_div] using hd,hr,by unfold kind; rw [hd,hr]; norm_num [bits]⟩

theorem counterexample : (D {0,2}).Nonempty ∧ 1 ≤ N {0,2} ∧ ¬ Const usual f (D {0,2}) := by
  have hx : pt 0 ∈ D {0,2} := mem_realSet.2 (Or.inl rfl)
  have hy : pt 2 ∈ D {0,2} := mem_realSet.2 (Or.inr rfl)
  refine ⟨⟨_,hx⟩,by rw [pairValue]; norm_num,fun h => ?_⟩
  have H := h _ hx _ hy
  norm_num [f,usual] at H
end
end MG.Floor
