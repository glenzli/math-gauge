import CH03.Exercises
import CH03.LineExamples

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open Set

set_option maxHeartbeats 5000000

/-- The floor function on the four domains used in Exercise 3.4. -/
noncomputable def floorOp : Operator (Option ℝ) none where
  func
    | none => none
    | some x => some (if x < 1 then 0 else if x < 2 then 1 else 2)
  preserves_bot := rfl

def D1 : Set (Option ℝ) := some '' Set.Icc (0 : ℝ) (1/2)
def D2 : Set (Option ℝ) := some '' Set.Icc (9/10 : ℝ) (11/10)
def D3 : Set (Option ℝ) := {some (0 : ℝ), some 2}
def D4 : Set (Option ℝ) := some '' Set.Icc (0 : ℝ) 2

theorem mem_D1 {x : Option ℝ} :
    x ∈ D1 ↔ ∃ r : ℝ, x = some r ∧ 0 ≤ r ∧ r ≤ 1/2 := by
  unfold D1
  constructor
  · rintro ⟨r, hr, hxr⟩
    exact ⟨r, hxr.symm, hr.1, hr.2⟩
  · rintro ⟨r, rfl, hr0, hr1⟩
    exact ⟨r, ⟨hr0, hr1⟩, rfl⟩

theorem mem_D2 {x : Option ℝ} :
    x ∈ D2 ↔ ∃ r : ℝ, x = some r ∧ 9/10 ≤ r ∧ r ≤ 11/10 := by
  unfold D2
  constructor
  · rintro ⟨r, hr, hxr⟩
    exact ⟨r, hxr.symm, hr.1, hr.2⟩
  · rintro ⟨r, rfl, hr0, hr1⟩
    exact ⟨r, ⟨hr0, hr1⟩, rfl⟩

theorem mem_D3 {x : Option ℝ} :
    x ∈ D3 ↔ x = some (0 : ℝ) ∨ x = some 2 := by
  simp [D3]

theorem mem_D4 {x : Option ℝ} :
    x ∈ D4 ↔ ∃ r : ℝ, x = some r ∧ 0 ≤ r ∧ r ≤ 2 := by
  unfold D4
  constructor
  · rintro ⟨r, hr, hxr⟩
    exact ⟨r, hxr.symm, hr.1, hr.2⟩
  · rintro ⟨r, rfl, hr0, hr1⟩
    exact ⟨r, ⟨hr0, hr1⟩, rfl⟩

theorem diameter_some_Icc (a b : ℝ) (hab : a ≤ b) :
    diameterScale (fun _ : Unit => lineDist) () (some '' Set.Icc a b) =
      ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    rcases hx with ⟨xr, hxr, hvalx⟩
    rcases hy with ⟨yr, hyr, hvaly⟩
    subst x
    subst y
    change lineDist (some xr) (some yr) ≤ ENNReal.ofReal (b - a)
    rw [lineDist_some_some]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hxr.2, hyr.1], by linarith [hxr.1, hyr.2]⟩
  · have hx : some a ∈ some '' Set.Icc a b := ⟨a, ⟨le_rfl, hab⟩, rfl⟩
    have hy : some b ∈ some '' Set.Icc a b := ⟨b, ⟨hab, le_rfl⟩, rfl⟩
    calc
      ENNReal.ofReal (b - a) = lineDist (some a) (some b) := by
        rw [lineDist_some_some, abs_of_nonpos (by linarith)]
        ring_nf
      _ ≤ diameterScale (fun _ : Unit => lineDist) () (some '' Set.Icc a b) := by
        exact le_iSup_of_le (⟨some a, hx⟩ : {x : Option ℝ // x ∈ some '' Set.Icc a b})
          (le_iSup_of_le (⟨some b, hy⟩ : {x : Option ℝ // x ∈ some '' Set.Icc a b}) le_rfl)

theorem diameter_D1 : diameterScale (fun _ : Unit => lineDist) () D1 = ENNReal.ofReal (1/2 : ℝ) := by
  rw [D1, diameter_some_Icc 0 (1/2) (by norm_num)]
  ring_nf

theorem diameter_D2 : diameterScale (fun _ : Unit => lineDist) () D2 = ENNReal.ofReal (1/5 : ℝ) := by
  rw [D2, diameter_some_Icc (9/10) (11/10) (by norm_num)]
  ring_nf

theorem diameter_D4 : diameterScale (fun _ : Unit => lineDist) () D4 = (2 : ENNReal) := by
  rw [D4, diameter_some_Icc 0 2 (by norm_num)]
  norm_num

theorem diameter_D3 : diameterScale (fun _ : Unit => lineDist) () D3 = (2 : ENNReal) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro y
    rcases x with ⟨x, hx⟩
    rcases y with ⟨y, hy⟩
    simp only [D3, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num [lineDist]
  · exact le_iSup_of_le (⟨some 0, by simp [D3]⟩ : {x : Option ℝ // x ∈ D3})
      (le_iSup_of_le (⟨some 2, by simp [D3]⟩ : {y : Option ℝ // y ∈ D3}) (by norm_num [lineDist]))

end formal_oet.vol_01.ch_03_operator_local_degeneracy

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open Set

local notation "dL" => (fun _ : Unit => lineDist)

theorem floorOp_zero : floorOp.func (some (0:ℝ)) = some 0 := by norm_num [floorOp]
theorem floorOp_one : floorOp.func (some (1:ℝ)) = some 1 := by norm_num [floorOp]
theorem floorOp_two : floorOp.func (some (2:ℝ)) = some 2 := by norm_num [floorOp]

theorem floorOp_of_nonneg_lt_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    floorOp.func (some x) = some 0 := by
  simp [floorOp, h1]

theorem pointwiseRadius_eq_zero_of_no_legal
    (y : Option ℝ) (U : Set (Option ℝ))
    (h : ∀ r : ENNReal, LegalRadius lineDist (fun a b => lineDist a b = 0)
      floorOp y U r → False) :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp y U = 0 := by
  apply le_antisymm
  · unfold pointwiseRadius
    apply iSup_le
    intro r
    exact False.elim (h r r.2)
  · exact zero_le _

theorem pointwise_D2_one_zero :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 1) D2 = 0 := by
  apply pointwiseRadius_eq_zero_of_no_legal
  intro r hr
  have hrrealpos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr.1) hr.2.1
  let a : ℝ := min (r.toReal / 2) (1/10)
  have hapos : 0 < a := lt_min (by linarith) (by norm_num)
  have hahalf : a ≤ 1/10 := min_le_right _ _
  have har : a < r.toReal := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let x : ℝ := 1 - a
  have hxU : some x ∈ D2 := by
    rw [mem_D2]
    refine ⟨x, rfl, ?_, ?_⟩ <;> dsimp [x] <;> linarith
  have hxl : x < 1 := by dsimp [x]; linarith
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hdist : lineDist (some x) (some 1) < r := by
    rw [lineDist_some_some]
    apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.1).mpr
    have : |x - 1| = a := by
      rw [abs_of_neg]
      · dsimp [x]; ring
      · dsimp [x]; linarith
    rw [this]
    exact har
  have hzero := hr.2.2 (some x) hxU hdist
  change lineDist (floorOp.func (some x)) (floorOp.func (some 1)) = 0 at hzero
  rw [floorOp_of_nonneg_lt_one hx0 hxl, floorOp_one] at hzero
  have hone : lineDist (some (0:ℝ)) (some 1) = 1 := by norm_num [lineDist]
  rw [hone] at hzero
  norm_num at hzero

theorem pointwise_D4_one_zero :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 1) D4 = 0 := by
  apply pointwiseRadius_eq_zero_of_no_legal
  intro r hr
  have hrrealpos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr.1) hr.2.1
  let a : ℝ := min (r.toReal / 2) (1/2)
  have hapos : 0 < a := lt_min (by linarith) (by norm_num)
  have hahalf : a ≤ 1/2 := min_le_right _ _
  have har : a < r.toReal := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let x : ℝ := 1 - a
  have hxU : some x ∈ D4 := by
    rw [mem_D4]
    refine ⟨x, rfl, ?_, ?_⟩ <;> dsimp [x] <;> linarith
  have hxl : x < 1 := by dsimp [x]; linarith
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hdist : lineDist (some x) (some 1) < r := by
    rw [lineDist_some_some]
    apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) hr.2.1).mpr
    have : |x - 1| = a := by
      rw [abs_of_neg]
      · dsimp [x]; ring
      · dsimp [x]; linarith
    rw [this]
    exact har
  have hzero := hr.2.2 (some x) hxU hdist
  change lineDist (floorOp.func (some x)) (floorOp.func (some 1)) = 0 at hzero
  rw [floorOp_of_nonneg_lt_one hx0 hxl, floorOp_one] at hzero
  have hone : lineDist (some (0:ℝ)) (some 1) = 1 := by norm_num [lineDist]
  rw [hone] at hzero
  norm_num at hzero

end formal_oet.vol_01.ch_03_operator_local_degeneracy
namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open Set

local notation "dL" => (fun _ : Unit => lineDist)

theorem pointwise_D3_zero :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 0) D3 = 2 := by
  apply le_antisymm
  · unfold pointwiseRadius
    apply iSup_le
    intro rsub
    rcases rsub with ⟨r, hlegal⟩
    rcases hlegal with ⟨hr0, hrtop, hall⟩
    by_contra hnot
    have hlt : (2 : ENNReal) < r := lt_of_not_ge hnot
    have hx : some (2:ℝ) ∈ D3 := by simp [D3]
    have hdist : lineDist (some 2) (some 0) < r := by norm_num [lineDist]; exact hlt
    have hzero := hall (some 2) hx hdist
    change lineDist (floorOp.func (some 2)) (floorOp.func (some 0)) = 0 at hzero
    rw [floorOp_two, floorOp_zero] at hzero
    have htwo : lineDist (some (2:ℝ)) (some 0) = 2 := by norm_num [lineDist]
    rw [htwo] at hzero
    norm_num at hzero
  · apply le_pointwiseRadius_of_legal
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro x hx hlt
    simp only [D3, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · rw [floorOp_zero]
      norm_num [lineDist]
    · exfalso
      norm_num [lineDist] at hlt

theorem pointwise_D3_two :
    pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 2) D3 = 2 := by
  apply le_antisymm
  · unfold pointwiseRadius
    apply iSup_le
    intro rsub
    rcases rsub with ⟨r, hlegal⟩
    rcases hlegal with ⟨hr0, hrtop, hall⟩
    by_contra hnot
    have hlt : (2 : ENNReal) < r := lt_of_not_ge hnot
    have hx : some (0:ℝ) ∈ D3 := by simp [D3]
    have hdist : lineDist (some 0) (some 2) < r := by norm_num [lineDist]; exact hlt
    have hzero := hall (some 0) hx hdist
    change lineDist (floorOp.func (some 0)) (floorOp.func (some 2)) = 0 at hzero
    rw [floorOp_zero, floorOp_two] at hzero
    have htwo : lineDist (some (0:ℝ)) (some 2) = 2 := by norm_num [lineDist]
    rw [htwo] at hzero
    norm_num at hzero
  · apply le_pointwiseRadius_of_legal
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro x hx hlt
    simp only [D3, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exfalso
      norm_num [lineDist] at hlt
    · rw [floorOp_two]
      norm_num [lineDist]

theorem zeroing_D3 : zeroingMatrix dL floorOp D3 () () = 2 := by
  unfold zeroingMatrix unifiedRadius
  apply le_antisymm
  · calc
      (⨅ y : {y : Option ℝ // y ∈ D3},
          pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp y.1 D3)
          ≤ pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 0) D3 :=
            iInf_le _ (⟨some 0, by simp [D3]⟩ : {y : Option ℝ // y ∈ D3})
      _ = 2 := pointwise_D3_zero
  · apply le_iInf
    intro y
    have hy : y.1 = some (0:ℝ) ∨ y.1 = some 2 := by
      simpa only [D3, Set.mem_insert_iff, Set.mem_singleton_iff] using y.2
    rcases hy with h | h
    · rw [h]; exact pointwise_D3_zero.ge
    · rw [h]; exact pointwise_D3_two.ge

theorem zeroing_D2_zero : zeroingMatrix dL floorOp D2 () () = 0 := by
  apply le_antisymm
  · calc
      zeroingMatrix dL floorOp D2 () ()
          ≤ pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 1) D2 := by
            unfold zeroingMatrix unifiedRadius
            exact iInf_le _ (⟨some 1, by rw [mem_D2]; exact ⟨1, rfl, by norm_num, by norm_num⟩⟩ : {y : Option ℝ // y ∈ D2})
      _ = 0 := pointwise_D2_one_zero
  · exact zero_le _

theorem zeroing_D4_zero : zeroingMatrix dL floorOp D4 () () = 0 := by
  apply le_antisymm
  · calc
      zeroingMatrix dL floorOp D4 () ()
          ≤ pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp (some 1) D4 := by
            unfold zeroingMatrix unifiedRadius
            exact iInf_le _ (⟨some 1, by rw [mem_D4]; exact ⟨1, rfl, by norm_num, by norm_num⟩⟩ : {y : Option ℝ // y ∈ D4})
      _ = 0 := pointwise_D4_one_zero
  · exact zero_le _

theorem zeroing_D1_top : zeroingMatrix dL floorOp D1 () () = ⊤ := by
  apply le_antisymm le_top
  apply le_iInf
  intro y
  change ⊤ ≤ pointwiseRadius lineDist (fun a b => lineDist a b = 0) floorOp y.1 D1
  exact top_le_iff.mpr (pointwiseRadius_eq_top_iff.mpr (by
  intro r hr0 hrtop
  refine ⟨hr0, hrtop, ?_⟩
  intro x hx _
  change lineDist (floorOp.func x) (floorOp.func y.1) = 0
  rcases mem_D1.mp hx with ⟨xr, rfl, hx0, hx1⟩
  rcases mem_D1.mp y.2 with ⟨yr, hys, hy0, hy1⟩
  have hyr : y.1 = some yr := hys
  rw [hyr]
  rw [floorOp_of_nonneg_lt_one hx0 (by linarith),
    floorOp_of_nonneg_lt_one hy0 (by linarith)]
  norm_num [lineDist]))

end formal_oet.vol_01.ch_03_operator_local_degeneracy
namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open Set

local notation "dL" => (fun _ : Unit => lineDist)

noncomputable def diameterScaleFamily : InputScaleFamily (Option ℝ) Unit where
  scale := fun _ => diameterScale dL ()
  mono := by
    intro _ A B hAB
    exact diameterScale_mono dL () hAB

theorem ofReal_half_lt_one : ENNReal.ofReal (1/2 : ℝ) < (1 : ENNReal) := by
  rw [show (1:ENNReal) = ENNReal.ofReal (1:ℝ) by simp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1)).mpr (by norm_num)

theorem ofReal_fifth_lt_one : ENNReal.ofReal (1/5 : ℝ) < (1 : ENNReal) := by
  rw [show (1:ENNReal) = ENNReal.ofReal (1:ℝ) by simp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1)).mpr (by norm_num)

theorem type_D1 :
    thresholdType diameterScaleFamily 1 1 dL floorOp D1 () () = (true, true) := by
  have h1 : diameterScaleFamily.scale () D1 < (1 : ENNReal) := by
    change diameterScale dL () D1 < 1
    rw [diameter_D1]
    exact ofReal_half_lt_one
  have h2 : (1 : ENNReal) ≤ zeroingMatrix dL floorOp D1 () () := by
    rw [zeroing_D1_top]; exact le_top
  simp [thresholdType, h1, h2]

theorem type_D2 :
    thresholdType diameterScaleFamily 1 1 dL floorOp D2 () () = (true, false) := by
  have h1 : diameterScaleFamily.scale () D2 < (1 : ENNReal) := by
    change diameterScale dL () D2 < 1
    rw [diameter_D2]
    exact ofReal_fifth_lt_one
  have h2 : ¬ (1 : ENNReal) ≤ zeroingMatrix dL floorOp D2 () () := by
    rw [zeroing_D2_zero]
    norm_num
  simp [thresholdType, h1, h2]

theorem type_D3 :
    thresholdType diameterScaleFamily 1 1 dL floorOp D3 () () = (false, true) := by
  have h1 : ¬ diameterScaleFamily.scale () D3 < (1 : ENNReal) := by
    change ¬ diameterScale dL () D3 < 1
    rw [diameter_D3]
    norm_num
  have h2 : (1 : ENNReal) ≤ zeroingMatrix dL floorOp D3 () () := by
    rw [zeroing_D3]
    norm_num
  simp [thresholdType, h1, h2]

theorem type_D4 :
    thresholdType diameterScaleFamily 1 1 dL floorOp D4 () () = (false, false) := by
  have h1 : ¬ diameterScaleFamily.scale () D4 < (1 : ENNReal) := by
    change ¬ diameterScale dL () D4 < 1
    rw [diameter_D4]
    norm_num
  have h2 : ¬ (1 : ENNReal) ≤ zeroingMatrix dL floorOp D4 () () := by
    rw [zeroing_D4_zero]
    norm_num
  simp [thresholdType, h1, h2]

theorem radius_D3_ge_one : (1 : ENNReal) ≤ zeroingMatrix dL floorOp D3 () () := by
  rw [zeroing_D3]; norm_num

theorem D3_radius_not_forall_zero :
    (1 : ENNReal) ≤ zeroingMatrix dL floorOp D3 () () ∧
      ¬ (∀ x ∈ D3, ∀ y ∈ D3,
        lineDist (floorOp.func x) (floorOp.func y) = 0) := by
  constructor
  · exact radius_D3_ge_one
  · intro h
    have h02 := h (some 0) (by simp [D3]) (some 2) (by simp [D3])
    rw [floorOp_zero, floorOp_two] at h02
    have htwo : lineDist (some (0:ℝ)) (some 2) = 2 := by norm_num [lineDist]
    rw [htwo] at h02
    norm_num at h02

end formal_oet.vol_01.ch_03_operator_local_degeneracy
