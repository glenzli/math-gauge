import Models
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

abbrev usual := realDist id
abbrev pt := @some ℝ

theorem usual_eq {x y : ℝ} : usual x y = 0 ↔ x = y := by simp [usual,realDist,abs_nonpos_iff,sub_eq_zero]

theorem uniform_at (S : Set ℝ) (f : ℝ → ℝ) {x : ℝ} (hx : x ∈ S) :
    uniform usual usual f S S ≤ rad usual usual f S x := iInf_le _ (⟨x,hx⟩ : S)

theorem zero_tests {v : ENNReal} (h : ∀ t : ℝ, 0 < t → v < ENNReal.ofReal t) : v = 0 := by
  by_contra hn
  obtain ⟨r,hp,hr⟩ := exists_between (pos_iff_ne_zero.mpr hn)
  have ht : r ≠ ⊤ := (hr.trans_le le_top).ne
  have hh := h r.toReal (ENNReal.toReal_pos hp.ne' ht)
  rw [ENNReal.ofReal_toReal ht] at hh
  exact hr.asymm hh

def step (x : ℝ) : ℝ := if x < 0 then 0 else 1
def punct : Set ℝ := Ico (-1) 0 ∪ Ioc 0 1

theorem step_model : ExtendedPseudoMetric (Option ℝ) none (line id) ∧
    (area punct).Nonempty ∧ area punct ⊆ dom (run step) :=
  ⟨line_metric _,⟨pt 1,some_area.mpr (Or.inr ⟨by norm_num,le_rfl⟩)⟩,area_dom _ _⟩

theorem step_legal {y : ℝ} (hy : y ∈ punct) {r : ENNReal} :
    r ∈ legal usual usual step punct y ↔ PosFin r ∧ r ≤ ENNReal.ofReal |y| := by
  have hy' : (-1 ≤ y ∧ y < 0) ∨ (0 < y ∧ y ≤ 1) := hy
  constructor
  · rintro ⟨hr,h⟩
    refine ⟨hr,?_⟩
    by_contra! hh
    have hd := (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg y) hr.2.ne).mp hh
    let a := min 1 ((r.toReal - |y|)/2)
    have ha : 0 < a := lt_min (by norm_num) (by linarith)
    have ha1 : a ≤ 1 := min_le_left _ _
    have har : a < r.toReal - |y| := (min_le_right _ _).trans_lt (by linarith)
    rcases hy' with hy | hy
    · have hp : a ∈ punct := Or.inr ⟨ha,ha1⟩
      have hlt : usual a y < r := by
        apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne).mpr
        simp only [id_eq,abs_of_nonneg (by linarith : 0 ≤ a-y)]
        rw [abs_of_neg hy.2] at har
        linarith
      have := usual_eq.mp (h a hp hlt)
      simp [step,ha.not_gt,hy.2] at this
    · have hp : -a ∈ punct := Or.inl ⟨by linarith,by linarith⟩
      have hlt : usual (-a) y < r := by
        apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.ne).mpr
        simp only [id_eq,abs_of_neg (by linarith : -a-y < 0)]
        rw [abs_of_pos hy.1] at har
        linarith
      have := usual_eq.mp (h (-a) hp hlt)
      simp [step,neg_lt_zero.mpr ha,hy.1.not_gt] at this
  · rintro ⟨hr,hle⟩
    refine ⟨hr,?_⟩
    intro x hx hxy
    have h := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)).mp (hxy.trans_le hle)
    change |x-y| < |y| at h
    apply usual_eq.mpr
    rcases hy' with hy | hy
    · rw [abs_of_neg hy.2, abs_lt] at h
      simp [step,hy.2,show x < 0 by linarith]
    · rw [abs_of_pos hy.1, abs_lt] at h
      simp [step,hy.1.not_gt,show ¬ x < 0 by linarith]

theorem step_radius {y : ℝ} (hy : y ∈ punct) :
    rad (line id) (line id) (run step).func (area punct) (pt y) = ENNReal.ofReal |y| ∧
    0 < ENNReal.ofReal |y| := by
  have hn : y ≠ 0 := by rintro rfl; norm_num [punct] at hy
  have hp := ENNReal.ofReal_pos.mpr (abs_pos.mpr hn)
  rw [area_rad]
  exact ⟨le_antisymm (sSup_le fun _ hr => ((step_legal hy).mp hr).2)
    (le_sSup ((step_legal hy).mpr ⟨⟨hp,ENNReal.ofReal_lt_top⟩,le_rfl⟩)),hp⟩

theorem step_uniform : uniform (line id) (line id) (run step).func (area punct) (area punct) = 0 := by
  rw [area_uniform]
  apply zero_tests
  intro t ht
  let a := min 1 (t/2)
  have hp : 0 < a := lt_min (by norm_num) (by linarith)
  have ha : a ∈ punct := Or.inr ⟨hp,min_le_left _ _⟩
  have hr := (step_radius ha).1
  rw [area_rad,abs_of_pos hp] at hr
  exact (uniform_at punct step ha).trans_lt (hr ▸
    (ENNReal.ofReal_lt_ofReal_iff ht).mpr ((min_le_right _ _).trans_lt (by linarith)))

def floorF (x : ℝ) := (⌊x⌋ : ℝ)

theorem interval_diam {a c : ℝ} (h : a ≤ c) :
    diameter usual (Icc a c) = ENNReal.ofReal (c-a) := by
  apply le_antisymm
  · apply diameter_le.mpr
    intro x hx y hy
    apply ENNReal.ofReal_le_ofReal
    change |x-y| ≤ c-a
    exact abs_le.mpr ⟨by linarith [hx.1,hx.2,hy.1,hy.2],by linarith [hx.1,hx.2,hy.1,hy.2]⟩
  · have hh := le_diameter (p := usual) (U := Icc a c) (right_mem_Icc.mpr h) (left_mem_Icc.mpr h)
    simpa [usual,realDist,abs_of_nonneg (sub_nonneg.mpr h)] using hh

theorem pair_diam {a c : ℝ} (h : a ≤ c) :
    diameter usual {a,c} = ENNReal.ofReal (c-a) := by
  apply le_antisymm
  · rw [← interval_diam h]
    exact diameter_le.mpr fun x hx y hy => le_diameter
      ((show ({a,c} : Set ℝ) ⊆ Icc a c by rintro z (rfl | hz); exact ⟨le_rfl,h⟩; rw [show z = c from hz]; exact ⟨h,le_rfl⟩) hx)
      ((show ({a,c} : Set ℝ) ⊆ Icc a c by rintro z (rfl | hz); exact ⟨le_rfl,h⟩; rw [show z = c from hz]; exact ⟨h,le_rfl⟩) hy)
  · have hh := le_diameter (p := usual) (U := {a,c}) (x := c) (y := a) (by simp) (by simp)
    simpa [usual,realDist,abs_of_nonneg (sub_nonneg.mpr h)] using hh

theorem scale_counter : diameter (line id) (area ({0} : Set ℝ)) = 0 ∧
    diameter (line id) (area ({0,1} : Set ℝ)) = 1 ∧
    diameter (line id) (area ({0} : Set ℝ)) < 1/2 ∧
    1/2 ≤ diameter (line id) (area ({0,1} : Set ℝ)) := by
  have ha := pair_diam (a := 0) (c := 1) (by norm_num)
  have hb := pair_diam (a := 0) (c := 0) le_rfl
  norm_num at ha hb
  simp only [area_diam,ha,hb]
  norm_num

theorem floor_cross {a c : ℝ} (ha : a < 1) (hc : 1 ≤ c) :
    uniform usual usual floorF (Icc a c) (Icc a c) = 0 := by
  apply zero_tests
  intro t ht
  let δ := min (min (1-a) (1/2)) (t/2)
  have hp : 0 < δ := lt_min (lt_min (by linarith) (by norm_num)) (by linarith)
  have h₁ : δ ≤ 1-a := (min_le_left _ _).trans (min_le_left _ _)
  have h₂ : δ ≤ 1/2 := (min_le_left _ _).trans (min_le_right _ _)
  have h₃ : δ < t := (min_le_right _ _).trans_lt (by linarith)
  have hx : 1-δ ∈ Icc a c := ⟨by linarith,by linarith⟩
  have hy : 1 ∈ Icc a c := ⟨ha.le,hc⟩
  have hz : ⌊1-δ⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by linarith,by linarith⟩
  have hs : 0 < usual (floorF 1) (floorF (1-δ)) := by norm_num [floorF,hz,usual,realDist]
  have hh := positive_sep (p := usual) hy hx hs
  apply hh.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff ht).mpr
  simpa [abs_of_pos hp] using h₃

def floorData (S : Set ℝ) :=
  (diameter (line id) (area S), uniform (line id) (line id) (run floorF).func (area S) (area S))
def floorType (S : Set ℝ) := bits (floorData S).1 (floorData S).2 1 1

theorem floor_model (S : Set ℝ) : ExtendedPseudoMetric _ none (line id) ∧
    area S ⊆ dom (run floorF) := ⟨line_metric _,area_dom _ _⟩

theorem floor_half : floorData (Icc 0 (1/2)) = (1/2,⊤) ∧ floorType (Icc 0 (1/2)) = (true,true) := by
  have H : Const usual floorF (Icc 0 (1/2)) := by
    intro x hx y hy
    have z (v : ℝ) (hv : v ∈ Icc 0 (1/2)) : ⌊v⌋ = 0 :=
      Int.floor_eq_zero_iff.mpr ⟨hv.1,by linarith [hv.2]⟩
    simp [usual,realDist,floorF,z _ hx,z _ hy]
  have h := (const_top (p := usual) H).2
  norm_num [floorType,floorData,area_diam,area_uniform,interval_diam (by norm_num : (0:ℝ) ≤ 1/2),h,bits,ENNReal.ofReal_div_of_pos]

theorem floor_narrow : floorData (Icc (9/10) (11/10)) = (1/5,0) ∧
    floorType (Icc (9/10) (11/10)) = (true,false) := by
  norm_num [floorType,floorData,area_diam,area_uniform,
    interval_diam (by norm_num : (9/10:ℝ) ≤ 11/10),
    floor_cross (by norm_num : (9/10:ℝ) < 1) (by norm_num : (1:ℝ) ≤ 11/10),
    bits,ENNReal.ofReal_div_of_pos]

theorem floor_pair : floorData {0,2} = (2,2) ∧ floorType {0,2} = (false,true) ∧
    ¬ Const (line id) (run floorF).func (area {0,2}) := by
  have lo : 2 ≤ uniform usual usual floorF {0,2} {0,2} := by
    apply le_uniform.mpr
    norm_num [usual,realDist,floorF]
  have hi := positive_sep (p := usual) (U := ({0,2} : Set ℝ)) (x := 0) (y := 2)
    (by simp) (by simp) (by norm_num [usual,realDist,floorF] : 0 < usual (floorF 0) (floorF 2))
  have eq : uniform usual usual floorF {0,2} {0,2} = 2 :=
    le_antisymm (by simpa [usual,realDist] using hi) lo
  have hn : ¬ Const (line id) (run floorF).func (area {0,2}) := by
    intro h
    have := h (pt 0) (some_area.mpr (by simp)) (pt 2) (some_area.mpr (by simp))
    norm_num [pt,floorF] at this
  norm_num [floorData,floorType,area_diam,area_uniform,pair_diam (by norm_num : (0:ℝ) ≤ 2),
    eq,bits,hn]

theorem floor_wide : floorData (Icc 0 2) = (2,0) ∧ floorType (Icc 0 2) = (false,false) := by
  norm_num [floorType,floorData,area_diam,area_uniform,interval_diam (by norm_num : (0:ℝ) ≤ 2),
    floor_cross (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) ≤ 2),bits]

theorem floor_counter : 1 ≤ (floorData {0,2}).2 ∧ ¬ Const (line id) (run floorF).func (area {0,2}) :=
  ⟨by rw [floor_pair.1]; norm_num,floor_pair.2.2⟩

end
end C3
