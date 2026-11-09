import Chapter3.Examples

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
open scoped Classical

theorem uniform_pair {X : Type} {bot : X} (din dout : X → X → ENNReal)
    (hi : ExtendedPseudoMetric X bot din) (ho : ExtendedPseudoMetric X bot dout)
    (f : Operator X bot) (a b : X) (hab : 0 < dout (f.func a) (f.func b)) :
    uniformRadius din dout f {a,b} {a,b} = din a b := by
  apply le_antisymm (output_separation (by simp) (by simp) hab)
  apply (le_uniform_iff _ _ _ _ _ _).mpr
  intro y hy x hx hxy
  rcases hx with rfl | hx <;> rcases hy with rfl | hy
  · exact ho.dist_self _
  · have : y = b := hy; subst y; exact (lt_irrefl _ hxy).elim
  · have : x = b := hx; subst x
    rw [hi.symm] at hxy; exact (lt_irrefl _ hxy).elim
  · have hx' : x = b := hx; have hy' : y = b := hy; subst x; subst y
    exact ho.dist_self _

noncomputable def step : Operator (Option ℝ) none := liftOperator (fun x => if x < 0 then 0 else 1)
def stepDomain : Set (Option ℝ) := some '' (Ico (-1 : ℝ) 0 ∪ Ioc 0 1)
theorem step_valid :
    ExtendedPseudoMetric (Option ℝ) none (realGauge id) ∧
    stepDomain.Nonempty ∧ stepDomain ⊆ dom step := by
  refine ⟨realGauge_valid id,⟨some 1,1,by norm_num,rfl⟩,?_⟩
  rintro _ ⟨x,hx,rfl⟩; simp [dom,step,liftOperator]

noncomputable def floorOperator : Operator (Option ℝ) none := liftOperator (fun x => (⌊x⌋ : ℤ))
def floorPair : Set (Option ℝ) := {some 0,some 2}

theorem floor_pair :
    floorPair.Nonempty ∧ floorPair ⊆ dom floorOperator ∧
    diameter (realGauge id) floorPair = 2 ∧
    uniformRadius (realGauge id) (realGauge id) floorOperator floorPair floorPair = 2 ∧
    thresholdType (diameter (realGauge id) floorPair)
      (uniformRadius (realGauge id) (realGauge id) floorOperator floorPair floorPair) 1 1 = (false,true) ∧
    ¬ (∀ x ∈ floorPair, ∀ y ∈ floorPair, realGauge id (floorOperator.func x) (floorOperator.func y) = 0) := by
  have hd : diameter (realGauge id) floorPair = 2 := by
    simpa [floorPair] using real_diameter_pair 0 2
  have hp : 0 < realGauge id (floorOperator.func (some 0)) (floorOperator.func (some 2)) := by
    norm_num [floorOperator,liftOperator,realGauge,liftDistance]
  have hr : uniformRadius (realGauge id) (realGauge id) floorOperator floorPair floorPair = 2 := by
    simpa [floorPair,realGauge,liftDistance] using
      uniform_pair (realGauge id) (realGauge id) (realGauge_valid id) (realGauge_valid id) floorOperator
        (some 0) (some 2) hp
  refine ⟨⟨some 0,by simp [floorPair]⟩,?_,hd,hr,?_,?_⟩
  · intro x hx; rcases hx with rfl | hx
    · simp [dom,floorOperator,liftOperator]
    · have : x = some 2 := hx; subst x; simp [dom,floorOperator,liftOperator]
  · norm_num [thresholdType,hd,hr]
  · intro h; exact (ne_of_gt hp) (h _ (by simp [floorPair]) _ (by simp [floorPair]))

def translate : Operator (Option ℝ) none := liftOperator (fun x => x+1)
def translateDomain : Set (Option ℝ) := {some (-3),some (-2),some 0,some 2}
def translateImage : Set (Option ℝ) := {some (-2),some (-1),some 1,some 3}

theorem translate_image : translate.func '' translateDomain = translateImage := by
  ext x
  norm_num [translate,translateDomain,translateImage,liftOperator,eq_comm]

theorem translate_fibers :
    translateDomain ⊆ dom translate ∧
    (∀ x ∈ translateDomain,
      fiber absGauge (1 : Operator (Option ℝ) none) univ x translateDomain =
        if x = some (-3) then {some (-3)} else if x = some 0 then {some 0} else {some (-2),some 2}) ∧
    (∀ x ∈ translateDomain,
      fiber absGauge translate univ (translate.func x) translateDomain =
        if x = some (-3) then {some (-3)} else if x = some 2 then {some 2} else {some (-2),some 0}) := by
  refine ⟨?_,?_,?_⟩
  · intro x hx
    simp only [translateDomain,mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [dom,translate,liftOperator]
  all_goals
    intro x hx
    simp only [translateDomain,mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    all_goals
      ext y
      simp only [fiber,mem_setOf_eq]
      by_cases hy : y ∈ translateDomain
      · simp only [translateDomain,mem_insert_iff,mem_singleton_iff] at hy
        rcases hy with rfl | rfl | rfl | rfl <;>
          norm_num [translateDomain,translate,liftOperator,absGauge,realGauge,liftDistance]
      · simp only [translateDomain,mem_insert_iff,mem_singleton_iff,not_or] at hy
        norm_num [hy,translateDomain]

theorem cover_two_lower {X : Type} (d : X → X → ENNReal) (U : Set X) (hU : U.Nonempty)
    (ε : ENNReal) (h : ∀ c ∈ U, ∃ x ∈ U, ε ≤ d x c) : 2 ≤ covering_number d ε U := by
  classical
  apply le_iInf; intro S; apply le_iInf; intro hS
  obtain ⟨a,ha⟩ := hU
  obtain ⟨c,hc,_⟩ := hS.2 a ha
  obtain ⟨x,hx,hd⟩ := h c (hS.1 hc)
  obtain ⟨c',hc',hd'⟩ := hS.2 x hx
  have hne : c ≠ c' := by intro he; subst c'; exact (not_lt_of_ge hd) hd'
  have hsub : ({c,c'} : Finset X) ⊆ S := by simp [Finset.insert_subset_iff,hc,hc']
  have hcard := Finset.card_le_card hsub
  simp [hne] at hcard
  exact_mod_cast hcard

theorem translate_cover :
    covering_number (realGauge abs) (3/2) translateDomain = 2 ∧
    covering_number (realGauge abs) (3/2) (translate.func '' translateDomain) = 1 ∧
    ∃ hD : EntropyDefined (realGauge abs) (realGauge abs) translate translateDomain (3/2),
      entropyDifference (realGauge abs) (realGauge abs) translate translateDomain (3/2) hD = 1 := by
  have h15 : (1 : ENNReal) < 3/2 := by
    apply (ENNReal.lt_div_iff_mul_lt (by simp) (by simp)).mpr
    norm_num
  have h152 : (3/2 : ENNReal) ≤ 2 := by
    apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr
    norm_num
  have h153 : (3/2 : ENNReal) ≤ 3 := h152.trans (by norm_num)
  have hn : InternalEpsilonNet (realGauge abs) (3/2) translateDomain {some (-2),some 0} := by
    constructor
    · intro x hx; simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> norm_num [translateDomain]
    · intro x hx
      simp only [translateDomain,mem_insert_iff,mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact ⟨some (-2),by simp,by norm_num [realGauge,liftDistance]; exact h15⟩
      · exact ⟨some (-2),by simp,by norm_num [realGauge,liftDistance]⟩
      · exact ⟨some 0,by simp,by norm_num [realGauge,liftDistance]⟩
      · exact ⟨some (-2),by simp,by norm_num [realGauge,liftDistance]⟩
  have hi : covering_number (realGauge abs) (3/2) translateDomain = 2 := by
    apply le_antisymm
    · exact iInf_le_of_le {some (-2),some 0} (iInf_le_of_le hn (by norm_num))
    apply cover_two_lower _ _ ⟨some 0,by norm_num [translateDomain]⟩
    intro c hc
    simp only [translateDomain,mem_insert_iff,mem_singleton_iff] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨some 0,by norm_num [translateDomain],by norm_num [realGauge,liftDistance]; exact h153⟩
    · exact ⟨some 0,by norm_num [translateDomain],by norm_num [realGauge,liftDistance]; exact h152⟩
    · exact ⟨some (-2),by norm_num [translateDomain],by norm_num [realGauge,liftDistance]; exact h152⟩
    · exact ⟨some 0,by norm_num [translateDomain],by norm_num [realGauge,liftDistance]; exact h152⟩
  have ho : covering_number (realGauge abs) (3/2) (translate.func '' translateDomain) = 1 := by
    rw [translate_image]
    apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ ⟨some 1,by norm_num [translateImage]⟩)
    have hnet : InternalEpsilonNet (realGauge abs) (3/2) translateImage {some (-2)} := by
      constructor
      · simp [translateImage]
      · intro x hx
        refine ⟨some (-2),by simp,?_⟩
        simp only [translateImage,mem_insert_iff,mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl | rfl <;> norm_num [realGauge,liftDistance] <;> exact h15
    exact iInf_le_of_le _ (iInf_le_of_le hnet (by simp))
  refine ⟨hi,ho,Or.inr (ho ▸ ENNReal.one_lt_top),?_⟩
  norm_num [entropyDifference,metric_entropy,log2_ereal,hi,ho,Real.logb]

end Chapter3
