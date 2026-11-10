import Chapter3.MoreExamples

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
variable {X I : Type} {bot : X}

theorem finite_inf_attained [Fintype I] (a : I → ENNReal) (J : Set I) (hJ : J.Nonempty) :
    ∃ j ∈ J, (⨅ k ∈ J, a k) = a j := by
  letI : Nonempty J := hJ.to_subtype
  obtain ⟨j,hj⟩ := exists_eq_ciInf_of_finite (f := fun j : J => a j)
  exact ⟨j,j.property,by simpa only [iInf_subtype] using hj.symm⟩

theorem radius_min_attained [Fintype I] (d : I → X → X → ENNReal) (f : Operator X bot)
    (din : X → X → ENNReal) (U : Set X) (y : X) (J : Set I) (hJ : J.Nonempty) :
    ∃ j ∈ J, radius din (subfamily_pseudometric d J) f U y = radius din (d j) f U y := by
  rw [radius_subfamily]; exact finite_inf_attained _ J hJ

theorem uniform_min_attained [Fintype I] (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i : I) (J : Set I) (hJ : J.Nonempty) :
    ∃ j ∈ J, uniformRadius (d i) (subfamily_pseudometric d J) f U U = nullMatrix d f U j i := by
  rw [uniform_subfamily]; exact finite_inf_attained _ J hJ

noncomputable def subfamilyEntropyDifference (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J K : Set I) (ε : ENNReal)
    (h : EntropyDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f U ε) : EReal :=
  entropyDifference (subfamily_pseudometric d J) (subfamily_pseudometric d K) f U ε h

theorem subfamily_difference_representation (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J K : Set I) (ε : ENNReal)
    (h : EntropyDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f U ε) :
    subfamilyEntropyDifference d f U J K ε h =
      subfamily_metric_entropy d J ε U - subfamily_metric_entropy d K ε (f.func '' U) := rfl

theorem entropy_difference_finite (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) (ε : ENNReal)
    (hi : covering_number din ε U < ⊤) (ho : covering_number dout ε (f.func '' U) < ⊤)
    (hD : EntropyDefined din dout f U ε) :
    entropyDifference din dout f U ε hD =
      ((Real.logb 2 (covering_number din ε U).toReal -
        Real.logb 2 (covering_number dout ε (f.func '' U)).toReal : ℝ) : EReal) := by
  simp [entropyDifference,entropy_finite din U hU ε hi,entropy_finite dout _ (hU.image _) ε ho]

theorem entropy_difference_signs (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) (ε : ENNReal) (hD : EntropyDefined din dout f U ε) :
    (0 < entropyDifference din dout f U ε hD ↔ metric_entropy dout ε (f.func '' U) < metric_entropy din ε U) ∧
    (entropyDifference din dout f U ε hD < 0 ↔ metric_entropy din ε U < metric_entropy dout ε (f.func '' U)) ∧
    (entropyDifference din dout f U ε hD = 0 ↔ metric_entropy din ε U = metric_entropy dout ε (f.func '' U)) := by
  have ht : metric_entropy din ε U ≠ ⊤ ∨ metric_entropy dout ε (f.func '' U) ≠ ⊤ := by
    rcases hD with hi | ho
    · left; rw [entropy_finite din U hU ε hi]; simp
    · right; rw [entropy_finite dout _ (hU.image _) ε ho]; simp
  have hb : metric_entropy din ε U ≠ ⊥ ∨ metric_entropy dout ε (f.func '' U) ≠ ⊥ := by
    left; exact ne_of_gt (lt_of_lt_of_le (by simp) (metric_entropy_nonneg din ε U hU))
  refine ⟨EReal.sub_pos,EReal.sub_neg ht hb,?_⟩
  change _ - _ = 0 ↔ _ = _
  constructor
  · intro h
    exact le_antisymm (EReal.sub_nonpos.mp h.le) ((EReal.sub_nonneg ht hb).mp h.ge)
  · intro h
    exact le_antisymm (EReal.sub_nonpos.mpr h.le) ((EReal.sub_nonneg ht hb).mpr h.ge)

theorem swap_nonreverse :
    ¬ (activeComp (fun _ : Unit => twoD) swap two ∪
      activeComp (fun _ : Unit => twoD) swap (swap.func '' two) ⊆
      activeComp (fun _ : Unit => twoD) (swap * swap) two) ∧
    ¬ (idComp (fun _ : Unit => twoD) (swap * swap) two ⊆
      idComp (fun _ : Unit => twoD) swap two ∩
      idComp (fun _ : Unit => twoD) swap (swap.func '' two)) := by
  obtain ⟨_,_,him,ha,hi,hci,hca⟩ := swap_example
  simp [him,ha,hi,hci,hca]

theorem small_domain_cover (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (hA : A.Nonempty) {τs τn ε : ENNReal}
    (hs : diameter din A < τs) (hst : τs ≤ τn)
    (hn : τn ≤ uniformRadius din dout f A A) (he : 0 < ε) :
    covering_number dout ε (f.func '' A) = 1 :=
  constant_cover dout f A hA he ((small_domain_iff din dout f A hs hst).mp hn)

end Chapter3
