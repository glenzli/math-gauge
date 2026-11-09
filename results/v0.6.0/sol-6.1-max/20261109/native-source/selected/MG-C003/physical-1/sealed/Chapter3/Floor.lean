import Chapter3.Step

namespace Chapter3.Floor
open Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
noncomputable section
def value (x : ℝ) : ℝ := (⌊x⌋ : ℤ)
def f := pointedOp value
def D1 : Set (Option ℝ) := some '' Icc (0 : ℝ) (1/2)
def D2 : Set (Option ℝ) := some '' Icc (9/10 : ℝ) (11/10)
def D3 : Set (Option ℝ) := {some 0,some 2}
def D4 : Set (Option ℝ) := some '' Icc (0 : ℝ) 2

theorem domains : D1 ⊆ dom f ∧ D2 ⊆ dom f ∧ D3 ⊆ dom f ∧ D4 ⊆ dom f := by
  have him : ∀ S : Set ℝ, some '' S ⊆ dom f := by
    intro S
    rintro _ ⟨x,hx,rfl⟩
    simp [f,dom]
  refine ⟨him _,him _,?_,him _⟩
  intro x hx
  rcases hx with rfl | rfl <;> simp [f,dom]

theorem diameters : diameter realDistance D1 = 1/2 ∧ diameter realDistance D2 = 1/5 ∧
    diameter realDistance D3 = 2 ∧ diameter realDistance D4 = 2 := by
  constructor
  · norm_num [D1,diameter_real_interval (by norm_num : (0 : ℝ) ≤ 1/2),ENNReal.ofReal_div_of_pos]
  constructor
  · norm_num [D2,diameter_real_interval (by norm_num : (9/10 : ℝ) ≤ 11/10),ENNReal.ofReal_div_of_pos]
  constructor
  · norm_num [D3,diameter_pair realDistance realDistance_metric]
  · norm_num [D4,diameter_real_interval (by norm_num : (0 : ℝ) ≤ 2)]

theorem first_radius : uniformRadius realDistance realDistance f D1 D1 = ⊤ := by
  apply uniform_top_of_const
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  have hfx : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hx.1,by linarith [hx.2]⟩
  have hfy : ⌊y⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨hy.1,by linarith [hy.2]⟩
  simp [f,value,hfx,hfy]

theorem jump {r : ℝ} (hr : 0 < r) :
    ∃ x : ℝ, 9/10 ≤ x ∧ x < 1 ∧ |x-1| < r ∧ value x = 0 := by
  let t := min (1/20 : ℝ) (r/2)
  have ht : 0 < t := lt_min (by norm_num) (by linarith)
  have ht1 : t ≤ 1/20 := min_le_left _ _
  have htr : t ≤ r/2 := min_le_right _ _
  refine ⟨1-t,by linarith,by linarith,?_,?_⟩
  · rw [abs_of_neg (by linarith : 1-t-1<0)]
    linarith
  · have hf : ⌊1-t⌋ = (0 : ℤ) := Int.floor_eq_zero_iff.mpr ⟨by linarith,by linarith⟩
    simp [value,hf]

theorem second_radius : uniformRadius realDistance realDistance f D2 D2 = 0 := by
  apply uniform_zero_of_close
  intro r hr
  obtain ⟨x,hx,hx1,hxr,hfx⟩ := jump hr
  refine ⟨some x,mem_image_of_mem _ ⟨hx,by linarith⟩,
    some 1,mem_image_of_mem _ ⟨by norm_num,by norm_num⟩,?_,?_⟩
  · rw [realDistance_some]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hxr
  · simp only [f,pointedOp_some]
    rw [hfx]
    norm_num [value]

theorem third_radius : uniformRadius realDistance realDistance f D3 D3 = 2 := by
  simp only [uniformRadius,D3,iInf_pair,radius]
  norm_num [f,value]

theorem fourth_radius : uniformRadius realDistance realDistance f D4 D4 = 0 := by
  apply uniform_zero_of_close
  intro r hr
  obtain ⟨x,hx,hx1,hxr,hfx⟩ := jump hr
  refine ⟨some x,mem_image_of_mem _ ⟨by linarith,by linarith⟩,
    some 1,mem_image_of_mem _ ⟨by norm_num,by norm_num⟩,?_,?_⟩
  · rw [realDistance_some]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr hxr
  · simp only [f,pointedOp_some]
    rw [hfx]
    norm_num [value]

theorem types :
    thresholdType (diameter realDistance D1) (uniformRadius realDistance realDistance f D1 D1) 1 1 = (true,true) ∧
    thresholdType (diameter realDistance D2) (uniformRadius realDistance realDistance f D2 D2) 1 1 = (true,false) ∧
    thresholdType (diameter realDistance D3) (uniformRadius realDistance realDistance f D3 D3) 1 1 = (false,true) ∧
    thresholdType (diameter realDistance D4) (uniformRadius realDistance realDistance f D4 D4) 1 1 = (false,false) := by
  norm_num [diameters.1,diameters.2.1,diameters.2.2.1,diameters.2.2.2,
    first_radius,second_radius,third_radius,fourth_radius,thresholdType]

theorem counterexample :
    (1 : ENNReal) ≤ uniformRadius realDistance realDistance f D3 D3 ∧
    ¬ (∀ x ∈ D3, ∀ y ∈ D3, realDistance (f.func x) (f.func y) = 0) ∧
    (∀ x ∈ D3, ∀ y ∈ D3, realDistance x y < 2 → x=y) := by
  refine ⟨by rw [third_radius]; norm_num,?_,?_⟩
  · intro h
    have hh := h (some 0) (by simp [D3]) (some 2) (by simp [D3])
    norm_num [f,value] at hh
  · intro x hx y hy hxy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num at *

end
end Chapter3.Floor
