import Ch03.TranslationCovering

namespace OET.Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-- Diameter of the image of a real closed interval under `some`. -/
theorem diameter_closed_interval (a b : ℝ) (hab : a ≤ b) :
    diameter usualDist (some '' Set.Icc a b) = ENNReal.ofReal (b - a) := by
  apply le_antisymm
  · apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    rcases hx with ⟨x, hx, rfl⟩
    rcases hy with ⟨y, hy, rfl⟩
    apply ENNReal.ofReal_le_ofReal
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  · apply le_iSup_of_le (some a)
    apply le_iSup_of_le ⟨a, ⟨le_rfl, hab⟩, rfl⟩
    apply le_iSup_of_le (some b)
    apply le_iSup_of_le ⟨b, ⟨hab, le_rfl⟩, rfl⟩
    rw [usualDist_some, show |a - b| = b - a by rw [abs_sub_comm]; exact abs_of_nonneg (sub_nonneg.mpr hab)]

theorem diameter_pair (x y : RealBase) :
    diameter usualDist ({x, y} : Set RealBase) = usualDist x y := by
  apply le_antisymm
  · apply iSup_le
    intro a
    apply iSup_le
    intro ha
    apply iSup_le
    intro b
    apply iSup_le
    intro hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · simp [usualDist_extended.dist_self]
      · have : b = y := by simpa using hb
        subst b; exact le_rfl
    · have : a = y := by simpa using ha
      subst a
      rcases hb with rfl | hb
      · simpa [usualDist_extended.symm]
      · have : b = y := by simpa using hb
        subst b; simp [usualDist_extended.dist_self]
  · exact le_iSup_of_le x (le_iSup_of_le (by simp) (le_iSup_of_le y (le_iSup_of_le (by simp) le_rfl)))

/-- Proposition 3.14(iii), with the original two-point/one-point real example. -/
theorem diameter_reverse_scale_fails :
    let A : Set RealBase := {some 0, some 1}
    let B : Set RealBase := {some 0}
    diameter usualDist B < (1 / 2 : ENNReal) ∧ ¬ diameter usualDist A < (1 / 2 : ENNReal) := by
  dsimp
  constructor
  · rw [show ({some 0} : Set RealBase) = {some 0, some 0} by simp, diameter_pair]
    simp [usualDist, optionDist]
  · rw [diameter_pair]
    norm_num [usualDist, optionDist]

/-- Exercise 3.4: integer floor as an operator. -/
noncomputable def floorOp : Operator RealBase none where
  func
    | none => none
    | some x => some (⌊x⌋ : ℝ)
  preserves_bot := rfl

def floorDomain1 : Set RealBase := some '' Set.Icc 0 (1 / 2)
def floorDomain2 : Set RealBase := some '' Set.Icc (9 / 10) (11 / 10)
def floorDomain3 : Set RealBase := {some 0, some 2}
def floorDomain4 : Set RealBase := some '' Set.Icc 0 2

theorem floorOp_apply_zero {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    floorOp.func (some x) = some 0 := by
  have hf : ⌊x⌋ = 0 := by
    apply Int.floor_eq_iff.mpr
    norm_num
    exact ⟨hx0, hx1⟩
  simp [floorOp, hf]

/-- If `1` belongs to the evaluation domain and `y < 1`, then the floor
operator's pointwise radius at `y` is at most `1-y`. -/
theorem floor_radius_le_one_sub {D : Set RealBase} {y : ℝ}
    (hy : some y ∈ D) (hy0 : 0 ≤ y) (hy1 : y < 1) (h1 : some 1 ∈ D) :
    annihilationRadius floorOp usualDist usualDist (some y) D ≤ ENNReal.ofReal (1 - y) := by
  apply sSup_le
  intro r hr
  by_contra hnr
  have hgt : ENNReal.ofReal (1 - y) < r := lt_of_not_ge hnr
  have hreal : 1 - y < r.toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) (ne_of_lt hr.2.1)).mp hgt
  have hball : some 1 ∈ ball usualDist (some y) r ∩ D := by
    refine ⟨?_, h1⟩
    apply (ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) (ne_of_lt hr.2.1)).mpr
    rw [abs_of_nonneg (by linarith)]
    exact hreal
  have hz := (hr.2.2 hball).2
  rw [floorOp_apply_zero hy0 hy1] at hz
  have hf1 : floorOp.func (some 1) = some 1 := by norm_num [floorOp]
  rw [hf1] at hz
  norm_num [usualDist, optionDist] at hz

/-- Domain `[9/10,11/10]` has zero uniform radius. -/
theorem floorDomain2_uniform_zero :
    uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain2 = 0 := by
  apply nonpos_iff_eq_zero.mp
  by_contra hn
  have hpos : 0 < uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain2 := lt_of_not_ge hn
  obtain ⟨r, hr0, hrU⟩ := exists_between hpos
  have hrt : r < ⊤ := hrU.trans_le le_top
  have hrt0 : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr0) (ne_of_lt hrt)
  let δ := min (1 / 10 : ℝ) (r.toReal / 2)
  let y := 1 - δ
  have hδ0 : 0 < δ := lt_min (by norm_num) (half_pos hrt0)
  have hδsmall : δ ≤ 1 / 10 := min_le_left _ _
  have hδr : δ < r.toReal := (min_le_right _ _).trans_lt (half_lt_self hrt0)
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have hy1 : y < 1 := by dsimp [y]; linarith
  have hyD : some y ∈ floorDomain2 := by
    refine ⟨y, ⟨?_, ?_⟩, rfl⟩
    · dsimp [y]; linarith
    · dsimp [y]; linarith
  have h1D : some 1 ∈ floorDomain2 := ⟨1, ⟨by norm_num, by norm_num⟩, rfl⟩
  have hle : uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain2 ≤
      annihilationRadius floorOp usualDist usualDist (some y) floorDomain2 :=
    iInf_le (fun z : floorDomain2 => annihilationRadius floorOp usualDist usualDist z.1 floorDomain2)
      ⟨some y, hyD⟩
  have hle' := hle.trans (floor_radius_le_one_sub hyD hy0 hy1 h1D)
  have hδeq : 1 - y = δ := by dsimp [y]; ring
  rw [hδeq] at hle'
  have hδr' : ENNReal.ofReal δ < r :=
    (ENNReal.ofReal_lt_iff_lt_toReal hδ0.le (ne_of_lt hrt)).mpr hδr
  exact (not_lt_of_ge hle') (hδr'.trans hrU)

/-- Domain `[0,2]` also has zero uniform radius. -/
theorem floorDomain4_uniform_zero :
    uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain4 = 0 := by
  apply nonpos_iff_eq_zero.mp
  by_contra hn
  have hpos : 0 < uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain4 := lt_of_not_ge hn
  obtain ⟨r, hr0, hrU⟩ := exists_between hpos
  have hrt : r < ⊤ := hrU.trans_le le_top
  have hrt0 : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr0) (ne_of_lt hrt)
  let δ := min (1 : ℝ) (r.toReal / 2)
  let y := 1 - δ
  have hδ0 : 0 < δ := lt_min zero_lt_one (half_pos hrt0)
  have hδsmall : δ ≤ 1 := min_le_left _ _
  have hδr : δ < r.toReal := (min_le_right _ _).trans_lt (half_lt_self hrt0)
  have hy0 : 0 ≤ y := by dsimp [y]; linarith
  have hy1 : y < 1 := by dsimp [y]; linarith
  have hyD : some y ∈ floorDomain4 := ⟨y, ⟨hy0, by dsimp [y]; linarith⟩, rfl⟩
  have h1D : some 1 ∈ floorDomain4 := ⟨1, ⟨zero_le_one, by norm_num⟩, rfl⟩
  have hle : uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain4 ≤
      annihilationRadius floorOp usualDist usualDist (some y) floorDomain4 :=
    iInf_le (fun z : floorDomain4 => annihilationRadius floorOp usualDist usualDist z.1 floorDomain4)
      ⟨some y, hyD⟩
  have hle' := hle.trans (floor_radius_le_one_sub hyD hy0 hy1 h1D)
  have hδeq : 1 - y = δ := by dsimp [y]; ring
  rw [hδeq] at hle'
  have hδr' : ENNReal.ofReal δ < r :=
    (ENNReal.ofReal_lt_iff_lt_toReal hδ0.le (ne_of_lt hrt)).mpr hδr
  exact (not_lt_of_ge hle') (hδr'.trans hrU)

/-- The two-point domain `{0,2}` has uniform radius exactly two. -/
theorem floorDomain3_uniform_two :
    uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain3 = 2 := by
  have hpoint : ∀ y ∈ floorDomain3,
      annihilationRadius floorOp usualDist usualDist y floorDomain3 = 2 := by
    intro y hyD
    let z : ℝ := if y = some 0 then 2 else 0
    have hzD : some z ∈ floorDomain3 := by
      rcases hyD with rfl | hyD
      · simp [z, floorDomain3]
      · have : y = some 2 := by simpa [floorDomain3] using hyD
        subst y
        simp [z, floorDomain3]
    have hyz : usualDist (some z) y = 2 := by
      rcases hyD with rfl | hyD
      · norm_num [z, usualDist, optionDist]
      · have : y = some 2 := by simpa [floorDomain3] using hyD
        subst y
        norm_num [z, usualDist, optionDist]
    have hfyz : usualDist (floorOp.func (some z)) (floorOp.func y) = 2 := by
      rcases hyD with rfl | hyD
      · norm_num [z, floorOp, usualDist, optionDist]
      · have : y = some 2 := by simpa [floorDomain3] using hyD
        subst y
        norm_num [z, floorOp, usualDist, optionDist]
    apply le_antisymm
    · apply sSup_le
      intro r hr
      by_contra hnr
      have hgt : (2 : ENNReal) < r := lt_of_not_ge hnr
      have hball : some z ∈ ball usualDist y r ∩ floorDomain3 := by
        refine ⟨?_, hzD⟩
        change usualDist (some z) y < r
        rw [hyz]
        exact hgt
      have hz := (hr.2.2 hball).2
      rw [hfyz] at hz
      norm_num at hz
    · apply le_annihilationRadius_of_forall_lt
      intro r hr0 hrt hr2
      intro x hx
      by_cases hxy : x = y
      · subst x
        exact ⟨hyD, usualDist_extended.dist_self _⟩
      · have hxz : x = some z := by
          have hxD := hx.2
          rcases hyD with rfl | hyD
          · simp only [floorDomain3, mem_insert_iff, mem_singleton_iff] at hxD
            rcases hxD with rfl | hxD
            · exact (hxy rfl).elim
            · have : x = some 2 := by simpa using hxD
              subst x
              simp [z]
          · have hy2 : y = some 2 := by simpa [floorDomain3] using hyD
            subst y
            simp only [floorDomain3, mem_insert_iff, mem_singleton_iff] at hxD
            rcases hxD with rfl | hxD
            · simp [z]
            · have : x = some 2 := by simpa using hxD
              exact (hxy this).elim
        subst x
        have hdist : usualDist (some z) y < r := hx.1
        rw [hyz] at hdist
        exact False.elim ((not_lt_of_ge hr2.le) hdist)
  apply le_antisymm
  · rw [← hpoint (some 0) (by simp [floorDomain3])]
    exact iInf_le (fun y : floorDomain3 => annihilationRadius floorOp usualDist usualDist y.1 floorDomain3)
      ⟨some 0, by simp [floorDomain3]⟩
  · apply le_iInf
    intro y
    rw [hpoint y.1 y.2]

/-- All four diameter/radius/type computations in Exercise 3.4(i). -/
theorem floor_threshold_computations :
    (diameter usualDist floorDomain1 = ENNReal.ofReal (1 / 2) ∧
      uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain1 = ⊤) ∧
    (diameter usualDist floorDomain2 = ENNReal.ofReal (1 / 5) ∧
      uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain2 = 0) ∧
    (diameter usualDist floorDomain3 = 2 ∧
      uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain3 = 2) ∧
    (diameter usualDist floorDomain4 = 2 ∧
      uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain4 = 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · constructor
    · rw [floorDomain1, diameter_closed_interval 0 (1 / 2) (by norm_num)]
      norm_num
    · have hc : () ∈ constComponents (fun _ : Unit => usualDist) floorOp floorDomain1 := by
        rintro x ⟨x, hx, rfl⟩ y ⟨y, hy, rfl⟩
        rw [floorOp_apply_zero hx.1 (by linarith [hx.2]), floorOp_apply_zero hy.1 (by linarith [hy.2])]
        simp [usualDist, optionDist]
      have h := uniformRadius_top_of_const_subfamily (fun _ : Unit => usualDist) floorOp
        (show floorDomain1.Nonempty from ⟨some 0, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩)
        (J := {()}) (fun j hj => by simpa using hc) ()
      calc
        uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain1 =
            componentUniformAnnihilationRadius (fun _ : Unit => usualDist) floorOp () {()} floorDomain1 :=
          (componentUniformRadius_single (fun _ : Unit => usualDist) floorOp () () floorDomain1).symm
        _ = ⊤ := h.2
  · constructor
    · rw [floorDomain2, diameter_closed_interval (9 / 10) (11 / 10) (by norm_num)]
      norm_num
    · exact floorDomain2_uniform_zero
  · exact ⟨by rw [floorDomain3, diameter_pair]; norm_num [usualDist, optionDist], floorDomain3_uniform_two⟩
  · exact ⟨by rw [floorDomain4, diameter_closed_interval 0 2 (by norm_num)]; norm_num, floorDomain4_uniform_zero⟩

/-- The four threshold types at `τσ = τN = 1`. -/
theorem floor_threshold_types :
    (∃ h1 : floorDomain1.Nonempty, thresholdType
      (diameterScaleFamily (fun _ : Unit => usualDist)) (fun _ => usualDist) floorOp
      floorDomain1 h1 1 1 () () = (1, 1)) ∧
    (∃ h2 : floorDomain2.Nonempty, thresholdType
      (diameterScaleFamily (fun _ : Unit => usualDist)) (fun _ => usualDist) floorOp
      floorDomain2 h2 1 1 () () = (1, 0)) ∧
    (∃ h3 : floorDomain3.Nonempty, thresholdType
      (diameterScaleFamily (fun _ : Unit => usualDist)) (fun _ => usualDist) floorOp
      floorDomain3 h3 1 1 () () = (0, 1)) ∧
    (∃ h4 : floorDomain4.Nonempty, thresholdType
      (diameterScaleFamily (fun _ : Unit => usualDist)) (fun _ => usualDist) floorOp
      floorDomain4 h4 1 1 () () = (0, 0)) := by
  have hdata := floor_threshold_computations
  have hD1 : floorDomain1.Nonempty := ⟨some 0, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
  have hD2 : floorDomain2.Nonempty := ⟨some 1, ⟨1, ⟨by norm_num, by norm_num⟩, rfl⟩⟩
  have hD3 : floorDomain3.Nonempty := ⟨some 0, by simp [floorDomain3]⟩
  have hD4 : floorDomain4.Nonempty := ⟨some 0, ⟨0, ⟨le_rfl, by norm_num⟩, rfl⟩⟩
  have hs1 : ENNReal.ofReal (1 / 2 : ℝ) < (1 : ENNReal) := by
    have h := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr
      (by norm_num : (1 / 2 : ℝ) < 1)
    simpa using h
  have hs2 : ENNReal.ofReal (1 / 5 : ℝ) < (1 : ENNReal) := by
    have h := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr
      (by norm_num : (1 / 5 : ℝ) < 1)
    simpa using h
  refine ⟨⟨hD1, ?_⟩, ⟨hD2, ?_⟩, ⟨hD3, ?_⟩, ⟨hD4, ?_⟩⟩
  · simp [thresholdType, diameterScaleFamily, componentUniformRadius_single,
      hdata.1.1, hdata.1.2, hs1]
  · simp [thresholdType, diameterScaleFamily, componentUniformRadius_single,
      hdata.2.1.1, hdata.2.1.2, hs2]
  · simp [thresholdType, diameterScaleFamily, componentUniformRadius_single,
      hdata.2.2.1.1, hdata.2.2.1.2]
  · simp [thresholdType, diameterScaleFamily, componentUniformRadius_single,
      hdata.2.2.2.1, hdata.2.2.2.2]

/-- Exercise 3.4(ii): `{0,2}` refutes the implication without a diameter
condition. -/
theorem floorDomain3_counterexample :
    (1 : ENNReal) ≤ uniformAnnihilationRadiusOn floorOp usualDist usualDist floorDomain3 ∧
      ¬ ∀ x ∈ floorDomain3, ∀ y ∈ floorDomain3,
        usualDist (floorOp.func x) (floorOp.func y) = 0 := by
  rw [floorDomain3_uniform_two]
  constructor
  · norm_num
  · intro h
    have hz := h (some 0) (by simp [floorDomain3]) (some 2) (by simp [floorDomain3])
    norm_num [floorOp, usualDist, optionDist] at hz

end OET.Ch03
