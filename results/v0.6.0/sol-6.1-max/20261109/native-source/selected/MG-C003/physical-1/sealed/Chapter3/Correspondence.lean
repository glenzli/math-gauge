import Chapter3.Floor
import Chapter3.FiniteExercises
import Chapter3.Rearrangement

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
noncomputable section
variable {X I : Type} {bot : X}

def actualSteps : List (Operator X bot) → Set X → List (Operator X bot × Set X)
  | [], _ => []
  | f::fs, U => (f,U) :: actualSteps fs (f.func '' U)
def finalImage : List (Operator X bot) → Set X → Set X
  | [], U => U
  | f::fs, U => finalImage fs (f.func '' U)
theorem run_image (fs : List (Operator X bot)) (U : Set X) : (run fs).func '' U = finalImage fs U := by
  induction fs generalizing U with
  | nil => change id '' U = U; simp
  | cons f fs ih => simpa [run,finalImage,image_image,Function.comp_def] using ih (f.func '' U)
theorem chainActs_union (d : I → X → X → ENNReal) (fs : List (Operator X bot)) (U : Set X) :
    chainActs d fs U = ⋃ p ∈ actualSteps fs U, actComponents d p.1 p.2 := by
  induction fs generalizing U with
  | nil => simp [actualSteps,chainActs]
  | cons f fs ih =>
    rw [chainActs,ih]
    ext i
    simp [actualSteps]

theorem finite_inf_attained {J : Set I} (hfin : J.Finite) (hne : J.Nonempty) (a : I → ENNReal) :
    ∃ j ∈ J, (⨅ k ∈ J, a k) = a j ∧ ∀ k ∈ J, a j ≤ a k := by
  obtain ⟨j,hj,hmin⟩ := Set.exists_min_image J a hfin hne
  exact ⟨j,hj,le_antisymm (iInf_le_of_le j (iInf_le_of_le hj le_rfl))
    (le_iInf (fun k => le_iInf (fun hk => hmin k hk))),hmin⟩
theorem finite_sup_attained {J : Set I} (hfin : J.Finite) (hne : J.Nonempty) (a : I → ENNReal) :
    ∃ j ∈ J, (⨆ k : J, a k.1) = a j ∧ ∀ k ∈ J, a k ≤ a j := by
  obtain ⟨j,hj,hmax⟩ := Set.exists_max_image J a hfin hne
  exact ⟨j,hj,le_antisymm (iSup_le (fun k => hmax k.1 k.2))
    (le_iSup (fun k : J => a k.1) ⟨j,hj⟩),hmax⟩

theorem subfamily_is_max [Fintype I] (d : I → X → X → ENNReal)
    (J : Set I) (hne : J.Nonempty) (x y : X) :
    ∃ j ∈ J, subfamily_pseudometric d J x y = d j x y ∧ ∀ k ∈ J, d k x y ≤ d j x y :=
  finite_sup_attained (Set.toFinite J) hne (fun j => d j x y)

theorem fiber_partition (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (J : Set I) (U : Set X) :
    (∀ y ∈ f.func '' U, (fiber d f J y U).Nonempty) ∧
    (⋃ y ∈ f.func '' U, fiber d f J y U) = U ∧
    (∀ y ∈ f.func '' U, ∀ z ∈ f.func '' U,
      fiber d f J y U = fiber d f J z U ∨ Disjoint (fiber d f J y U) (fiber d f J z U)) :=
  ⟨fun _ hy => fiber_nonempty d hd f J U hy, fiber_cover d hd f J U,
    fun y _ z _ => fiber_equal_or_disjoint d hd f J y z U⟩
theorem point_minimum [Fintype I] (d : I → X → X → ENNReal) (din : X → X → ENNReal)
    (f : Operator X bot) (J : Set I) (hne : J.Nonempty) (y : X) (U : Set X) :
    ∃ j ∈ J, radius din (subfamily_pseudometric d J) f y U = radius din (d j) f y U ∧
      ∀ k ∈ J, radius din (d j) f y U ≤ radius din (d k) f y U := by
  rw [radius_subfamily]
  exact finite_inf_attained (Set.toFinite J) hne _
theorem uniform_minimum [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (J : Set I) (hne : J.Nonempty) (i : I) (U : Set X) :
    ∃ j ∈ J, uniformRadius (d i) (subfamily_pseudometric d J) f U U = nullMatrix d f U j i ∧
      ∀ k ∈ J, nullMatrix d f U j i ≤ nullMatrix d f U k i := by
  rw [uniform_subfamily]
  exact finite_inf_attained (Set.toFinite J) hne _

def channelType (s : InputScales X I) (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : {A : Set X // A.Nonempty}) (ts tn : ENNReal) (i j : I) : Bool × Bool :=
  thresholdType (s.scale i A) (nullMatrix d f A.1 j i) ts tn
theorem channelType_correspondence (s : InputScales X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : {A : Set X // A.Nonempty}) (ts tn : ENNReal) (i j : I) :
    channelType s d f A ts tn i j =
      (decide (s.scale i A < ts), decide (tn ≤ uniformRadius (d i) (d j) f A.1 A.1)) := rfl
theorem threshold_exhaustive (s n ts tn : ENNReal) :
    thresholdType s n ts tn = (true,true) ∨ thresholdType s n ts tn = (true,false) ∨
    thresholdType s n ts tn = (false,true) ∨ thresholdType s n ts tn = (false,false) := by
  cases h : thresholdType s n ts tn with
  | mk a b => cases a <;> cases b <;> simp
theorem threshold_unique (s n ts tn : ENNReal) : ∃! p : Bool × Bool, thresholdType s n ts tn = p :=
  ⟨thresholdType s n ts tn,rfl,fun _ h => h.symm⟩

theorem scale_threshold_channels_mono (s : InputScales X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : {A : Set X // A.Nonempty}) (tn : ENNReal)
    {ts ts' : ENNReal} (h : ts ≤ ts') :
    {p : I × I | (channelType s d f A ts tn p.1 p.2).1 = true} ⊆
      {p : I × I | (channelType s d f A ts' tn p.1 p.2).1 = true} := by
  intro p hp
  simp only [channelType,thresholdType,mem_setOf_eq,decide_eq_true_eq] at *
  exact hp.trans_le h
theorem null_threshold_channels_antitone (s : InputScales X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : {A : Set X // A.Nonempty}) (ts : ENNReal)
    {tn tn' : ENNReal} (h : tn ≤ tn') :
    {p : I × I | (channelType s d f A ts tn' p.1 p.2).2 = true} ⊆
      {p : I × I | (channelType s d f A ts tn p.1 p.2).2 = true} := by
  intro p hp
  simp only [channelType,thresholdType,mem_setOf_eq,decide_eq_true_eq] at *
  exact h.trans hp

theorem separated_criteria (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X)
    (hf : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, GaugeZeroRelated d a b → a=b)
    (hg : ∀ a ∈ g.func '' U, ∀ b ∈ g.func '' U, GaugeZeroRelated d a b → a=b) :
    (pointRelation f U ⊆ pointRelation g U ↔ zeroRelation d f U ⊆ zeroRelation d g U) ∧
    (pointRelation f U = pointRelation g U ↔ zeroRelation d f U = zeroRelation d g U) := by
  rw [separated_relations d hd f U hf,separated_relations d hd g U hg]
  exact ⟨Iff.rfl,Iff.rfl⟩

theorem fiber_chain (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) {m a b : ℕ}
    (h : ∀ k < m, fiberPreorder d U (f k) (f (k+1))) (hab : a ≤ b) (hbm : b ≤ m) :
    fiberPreorder d U (f a) (f b) := relation_chain (fun k => zeroRelation d (f k) U) h hab hbm
theorem fiber_chain_strict (d : I → X → X → ENNReal) (U : Set X)
    (f : ℕ → Operator X bot) {m r : ℕ}
    (h : ∀ k < m, fiberPreorder d U (f k) (f (k+1))) (hr : r < m)
    (hs : zeroRelation d (f r) U ⊂ zeroRelation d (f (r+1)) U) :
    zeroRelation d (f 0) U ⊂ zeroRelation d (f m) U ∧
      ∃ x y, (x,y) ∈ zeroRelation d (f m) U ∧ (x,y) ∉ zeroRelation d (f 0) U := by
  obtain ⟨hh,⟨x,y⟩,hp,hn⟩ := relation_chain_strict (fun k => zeroRelation d (f k) U) h hr hs
  exact ⟨hh,x,y,hp,hn⟩

theorem log2_top_iff (x : ENNReal) : log2_ereal x = ⊤ ↔ x = ⊤ := by
  by_cases hz : x=0
  · simp [hz,log2_ereal]
  by_cases ht : x=⊤ <;> simp [log2_ereal,hz,ht]

def subfamilyEntropyDifference (d : I → X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (J K : Set I) (_hJ : J.Nonempty) (_hK : K.Nonempty)
    (h : entropyDifferenceDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f eps U) :
    EReal := entropyDifference (subfamily_pseudometric d J) (subfamily_pseudometric d K) f eps U h
theorem subfamily_difference_correspondence (d : I → X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (J K : Set I) (hJ : J.Nonempty) (hK : K.Nonempty)
    (h : entropyDifferenceDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f eps U) :
    subfamilyEntropyDifference d f eps U J K hJ hK h =
      subfamily_metric_entropy d J eps U - subfamily_metric_entropy d K eps (f.func '' U) := rfl
theorem difference_excludes_indeterminate (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (h : entropyDifferenceDefined din dout f eps U) :
    ¬ (metric_entropy din eps U = ⊤ ∧ metric_entropy dout eps (f.func '' U) = ⊤) := by
  rintro ⟨hi,ho⟩
  have hic := (log2_top_iff _).mp hi
  have hoc := (log2_top_iff _).mp ho
  rcases h.2.2.2.2 with hfin | hfin
  · exact (ne_of_lt hfin) hic
  · exact (ne_of_lt hfin) hoc
theorem difference_finite (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (h : entropyDifferenceDefined din dout f eps U)
    (hi : covering_number din eps U < ⊤) (ho : covering_number dout eps (f.func '' U) < ⊤) :
    ∃ r : ℝ, entropyDifference din dout f eps U h = (r : EReal) := by
  obtain ⟨a,ha⟩ := entropy_finite din eps U h.1 hi
  obtain ⟨b,hb⟩ := entropy_finite dout eps _ (h.1.image _) ho
  exact ⟨a-b,by simp [entropyDifference,ha,hb]⟩
theorem difference_top (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (h : entropyDifferenceDefined din dout f eps U)
    (hi : covering_number din eps U = ⊤) (ho : covering_number dout eps (f.func '' U) < ⊤) :
    entropyDifference din dout f eps U h = ⊤ := by
  obtain ⟨b,hb⟩ := entropy_finite dout eps _ (h.1.image _) ho
  have hh : metric_entropy din eps U = ⊤ := (log2_top_iff _).mpr hi
  simp [entropyDifference,hh,hb]
theorem difference_bot (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (h : entropyDifferenceDefined din dout f eps U)
    (hi : covering_number din eps U < ⊤) (ho : covering_number dout eps (f.func '' U) = ⊤) :
    entropyDifference din dout f eps U h = ⊥ := by
  obtain ⟨a,ha⟩ := entropy_finite din eps U h.1 hi
  have hh : metric_entropy dout eps (f.func '' U) = ⊤ := (log2_top_iff _).mpr ho
  simp [entropyDifference,hh,ha]

theorem constant_difference_exists (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hne : U.Nonempty) (hdom : U ⊆ dom f) {j : I}
    (hj : j ∈ constComponents d f U) {eps : ENNReal} (he : 0 < eps) (hef : eps < ⊤) :
    ∃ h : entropyDifferenceDefined (d j) (d j) f eps U,
      entropyDifference (d j) (d j) f eps U h = metric_entropy (d j) eps U := by
  have h : entropyDifferenceDefined (d j) (d j) f eps U :=
    ⟨hne,hdom,he,hef,Or.inr (by rw [(constant_entropy d f U hne hj he).1]; norm_num)⟩
  exact ⟨h,constant_difference d f U hj h⟩

theorem swap_domain : Swap.U ⊆ dom Swap.f ∧ Swap.U ⊆ dom (Swap.f*Swap.f) := by
  constructor <;> intro x hx <;> rcases hx with rfl | rfl <;> simp [Swap.f,pointedOp,dom]
theorem infinite_domain : Infinite.U.Nonempty ∧ Infinite.U ⊆ dom (1 : Operator (Option Bool) none) := by
  exact ⟨⟨some false,by simp [Infinite.U,Swap.U]⟩,by
    intro x hx; rcases hx with rfl | rfl <;> simp [dom]⟩
theorem reverse_scale_domain :
    ({some (0 : ℝ),some 1} : Set (Option ℝ)) ⊆ dom (1 : Operator (Option ℝ) none) := by
  intro x hx; rcases hx with rfl | rfl <;> simp [dom]

theorem pointwise_not_uniform_cover :
    (∀ y ∈ Step.U, 0 < radius realDistance realDistance Step.f y Step.U) ∧
    ∀ tau : ENNReal, 0 < tau → tau < ⊤ → ∃ B : Set (Option ℝ),
      B ⊆ Step.U ∧ B.Nonempty ∧ covering_number realDistance tau B = 1 ∧
        covering_number realDistance (1/2) (Step.f.func '' B) = 2 := by
  refine ⟨Step.all_positive,?_⟩
  intro tau ht htf
  obtain ⟨a,ha,ha1,hclose,hsub,hin,hout⟩ := Step.no_uniform_cover ht htf
  exact ⟨{some (-a),some a},hsub,⟨some a,by simp⟩,hin,hout⟩

theorem same_value_square_fibers (g : Operator (Option ℝ) none) (c : ℝ)
    (h0 : g.func (some 0) = some c) (h1 : g.func (some 1) = some c) (y : Option ℝ) :
    some 0 ∈ componentFiber Affine.d (g*g) () y Affine.U ↔
      some 1 ∈ componentFiber Affine.d (g*g) () y Affine.U := by
  have hh := (Affine.same_value_square g c h0 h1).1
  simp only [componentFiber,mem_setOf_eq]
  rw [hh]
  simp [Affine.U]

end
end Chapter3
