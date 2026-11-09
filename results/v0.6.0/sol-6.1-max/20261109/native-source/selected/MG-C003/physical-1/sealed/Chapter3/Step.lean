import Chapter3.Models

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
noncomputable section

theorem uniform_zero_of_close (din dout : Option ℝ → Option ℝ → ENNReal)
    (f : Operator (Option ℝ) none) (U : Set (Option ℝ))
    (h : ∀ r : ℝ, 0 < r → ∃ x ∈ U, ∃ y ∈ U,
      din x y < ENNReal.ofReal r ∧ 0 < dout (f.func x) (f.func y)) :
    uniformRadius din dout f U U = 0 := by
  apply le_antisymm _ (zero_le _)
  by_contra hn
  obtain ⟨r,hr,hrn⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
  obtain ⟨x,hx,y,hy,hd,ho⟩ := h r (by exact_mod_cast hr)
  have hh := output_separation din dout f U hx hy ho
  have hrr : ENNReal.ofReal (r : ℝ) = (r : ENNReal) := ENNReal.ofReal_coe_nnreal
  exact not_lt_of_ge hh (hd.trans_le (by rw [hrr]; exact hrn.le))

namespace Step
def value (x : ℝ) : ℝ := if x < 0 then 0 else 1
def f := pointedOp value
def U : Set (Option ℝ) := some '' {y : ℝ | -1 ≤ y ∧ y ≤ 1 ∧ y ≠ 0}

theorem source_domain : U = some '' (Ico (-1 : ℝ) 0 ∪ Ioc 0 1) ∧ U ⊆ dom f := by
  constructor
  · apply congrArg (fun S : Set ℝ => some '' S)
    ext y
    simp only [mem_setOf_eq,mem_union,mem_Ico,mem_Ioc]
    constructor
    · rintro ⟨h1,h2,h3⟩
      rcases lt_or_gt_of_ne h3 with h | h
      · exact Or.inl ⟨h1,h⟩
      · exact Or.inr ⟨h,h2⟩
    · rintro (⟨h1,h2⟩ | ⟨h1,h2⟩) <;> exact ⟨by linarith,by linarith,by linarith⟩
  · rintro _ ⟨y,hy,rfl⟩
    simp [f,dom]

theorem opposite (y R : ℝ) (hy : -1 ≤ y ∧ y ≤ 1 ∧ y ≠ 0) (hR : |y| < R) :
    ∃ x : ℝ, (-1 ≤ x ∧ x ≤ 1 ∧ x ≠ 0) ∧ |x-y| < R ∧ value x ≠ value y := by
  let t := min (1/2 : ℝ) ((R-|y|)/2)
  have ht : 0 < t := lt_min (by norm_num) (by linarith)
  have ht1 : t ≤ 1/2 := min_le_left _ _
  have htR : t ≤ (R-|y|)/2 := min_le_right _ _
  by_cases hys : y < 0
  · refine ⟨t,⟨by linarith,by linarith,ne_of_gt ht⟩,?_,?_⟩
    · rw [abs_of_pos (by linarith : 0 < t-y)]
      rw [abs_of_neg hys] at htR
      linarith
    · simp [value,hys,not_lt_of_ge ht.le]
  · have hyp : 0 < y := lt_of_le_of_ne (le_of_not_gt hys) (Ne.symm hy.2.2)
    refine ⟨-t,⟨by linarith,by linarith,by linarith⟩,?_,?_⟩
    · rw [abs_of_neg (by linarith : -t-y < 0)]
      rw [abs_of_pos hyp] at htR
      linarith
    · simp [value,hys,show -t < 0 by linarith]

theorem point_radius {y : ℝ} (hy : -1 ≤ y ∧ y ≤ 1 ∧ y ≠ 0) :
    radius realDistance realDistance f (some y) U = ENNReal.ofReal |y| := by
  apply le_antisymm
  · by_contra hn
    obtain ⟨R,hR,hRn⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
    have hRy : |y| < (R : ℝ) := by
      rw [← ENNReal.ofReal_coe_nnreal] at hR
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg y)).mp hR
    obtain ⟨x,hx,hxy,hout⟩ := opposite y R hy hRy
    have hd : realDistance (some x) (some y) < radius realDistance realDistance f (some y) U := by
      rw [realDistance_some]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [abs_nonneg y] : 0 < (R : ℝ))).mpr hxy |>.trans
        (by simpa using hRn)
    have hz := radius_rule realDistance realDistance f (some y) U (mem_image_of_mem _ hx) hd
    exact hout (realDistance_zero _ _ |>.mp hz)
  · apply (le_radius_iff _ _ _ _ _ _).mpr
    rintro _ ⟨x,hx,rfl⟩ hxy
    have hay : 0 < |y| := abs_pos.mpr hy.2.2
    have hab : |x-y| < |y| :=
      (ENNReal.ofReal_lt_ofReal_iff hay).mp (by simpa using hxy)
    have hs : (x < 0) ↔ (y < 0) := by
      by_cases hys : y < 0
      · rw [abs_of_neg hys] at hab
        exact iff_of_true (by have hh := le_abs_self (x-y); linarith) hys
      · have hyp : 0 < y := lt_of_le_of_ne (le_of_not_gt hys) (Ne.symm hy.2.2)
        rw [abs_of_pos hyp] at hab
        exact iff_of_false (by have hh := neg_le_abs (x-y); linarith) hys
    simp [f,value,hs]

theorem admissible_exact {y : ℝ} (hy : -1 ≤ y ∧ y ≤ 1 ∧ y ≠ 0)
    {r : ENNReal} (hr : 0 < r) (hrf : r < ⊤) :
    admissible realDistance realDistance f (some y) U r ↔ r ≤ ENNReal.ofReal |y| := by
  rw [← point_radius hy,le_radius_iff]
  exact ⟨fun h => h.2.2,fun h => ⟨hr,hrf,h⟩⟩

theorem all_positive : ∀ y ∈ U, 0 < radius realDistance realDistance f y U := by
  rintro _ ⟨y,hy,rfl⟩
  rw [point_radius hy]
  exact ENNReal.ofReal_pos.mpr (abs_pos.mpr hy.2.2)

theorem uniform_zero : uniformRadius realDistance realDistance f U U = 0 := by
  apply uniform_zero_of_close
  intro r hr
  let a := min (1/2 : ℝ) (r/4)
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have ha1 : a ≤ 1/2 := min_le_left _ _
  have har : a ≤ r/4 := min_le_right _ _
  refine ⟨some (-a),mem_image_of_mem _ ⟨by linarith,by linarith,by linarith⟩,
    some a,mem_image_of_mem _ ⟨by linarith,by linarith,ne_of_gt ha⟩,?_,?_⟩
  · rw [realDistance_some]
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mpr
    rw [abs_of_neg (by linarith : -a-a<0)]
    linarith
  · norm_num [f,value,show -a<0 by linarith,not_lt_of_ge ha.le]

theorem no_uniform_cover {tau : ENNReal} (ht : 0 < tau) (htf : tau < ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2*a) < tau ∧
      ({some (-a),some a} : Set (Option ℝ)) ⊆ U ∧
      covering_number realDistance tau ({some (-a),some a} : Set (Option ℝ)) = 1 ∧
      covering_number realDistance (1/2) (f.func '' ({some (-a),some a} : Set (Option ℝ))) = 2 := by
  let a := min (1/2 : ℝ) (tau.toReal/4)
  have htr : 0 < tau.toReal := ENNReal.toReal_pos (ne_of_gt ht) (ne_of_lt htf)
  have ha : 0 < a := lt_min (by norm_num) (by linarith)
  have ha1 : a ≤ 1/2 := min_le_left _ _
  have har : a ≤ tau.toReal/4 := min_le_right _ _
  have hclose : ENNReal.ofReal (2*a) < tau := by
    rw [← ENNReal.ofReal_toReal (ne_of_lt htf)]
    apply (ENNReal.ofReal_lt_ofReal_iff htr).mpr
    linarith
  refine ⟨a,ha,by linarith,hclose,?_,?_,?_⟩
  · intro x hx
    rcases hx with rfl | rfl
    · exact mem_image_of_mem _ ⟨by linarith,by linarith,by linarith⟩
    · exact mem_image_of_mem _ ⟨by linarith,by linarith,ne_of_gt ha⟩
  · rw [cover_pair realDistance realDistance_metric.dist_self realDistance_metric.symm
      (by simp; linarith : some (-a) ≠ some a) ht]
    have hh : realDistance (some (-a)) (some a) < tau := by
      simpa [abs_of_neg (show -a-a<0 by linarith),show -(-a-a)=2*a by ring] using hclose
    rw [if_pos hh]
  · have himage : f.func '' ({some (-a),some a} : Set (Option ℝ)) = {some 0,some 1} := by
      simp [f,value,Set.image_insert_eq,Set.image_singleton,show -a<0 by linarith,not_lt_of_ge ha.le]
    rw [himage,cover_pair realDistance realDistance_metric.dist_self realDistance_metric.symm
      (by norm_num : some (0 : ℝ) ≠ some 1) (by norm_num)]
    norm_num
end Step

theorem reverse_scale_example :
    diameter realDistance ({some (0 : ℝ)} : Set (Option ℝ)) = 0 ∧
    diameter realDistance ({some (0 : ℝ),some 1} : Set (Option ℝ)) = 1 ∧
    ({some (0 : ℝ)} : Set (Option ℝ)) ⊆ {some 0,some 1} ∧
    diameter realDistance ({some (0 : ℝ)} : Set (Option ℝ)) < 1/2 ∧
    1/2 ≤ diameter realDistance ({some (0 : ℝ),some 1} : Set (Option ℝ)) := by
  have h1 : diameter realDistance ({some (0 : ℝ)} : Set (Option ℝ)) = 0 := by
    simpa using diameter_pair realDistance realDistance_metric 0 0
  have h2 : diameter realDistance ({some (0 : ℝ),some 1} : Set (Option ℝ)) = 1 := by
    simpa using diameter_pair realDistance realDistance_metric 0 1
  norm_num [h1,h2]

end
end Chapter3
