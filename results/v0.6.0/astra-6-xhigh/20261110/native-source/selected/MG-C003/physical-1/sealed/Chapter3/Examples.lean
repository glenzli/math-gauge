import Chapter3.Cover

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open Set
open scoped Classical

@[simp] theorem compose_apply {X : Type} {bot : X} (f g : Operator X bot) (x : X) :
    (g * f).func x = g.func (f.func x) := rfl
@[simp] theorem one_apply {X : Type} {bot : X} (x : X) :
    (1 : Operator X bot).func x = x := rfl

noncomputable def liftDistance {A : Type} (d : A → A → ENNReal) : Option A → Option A → ENNReal
  | none, none => 0
  | some x, some y => d x y
  | _, _ => ⊤

theorem liftDistance_valid {A : Type} [Nonempty A] (d : A → A → ENNReal)
    (hs : ∀ x, d x x = 0) (hc : ∀ x y, d x y = d y x)
    (ht : ∀ x y z, d x z ≤ d x y + d y z) :
    ExtendedPseudoMetric (Option A) none (liftDistance d) := by
  refine ⟨⟨some (Classical.choice inferInstance),by simp⟩,?_,?_,?_,?_⟩
  · intro x; cases x <;> simp [liftDistance,hs]
  · intro x y; cases x <;> cases y <;> simp [liftDistance,hc]
  · intro x y z; cases x <;> cases y <;> cases z <;> simp [liftDistance,ht]
  · intro x hx; cases x <;> simp_all [liftDistance]

noncomputable def discreteRead {A B : Type} (q : A → B) (c : ENNReal) (x y : A) : ENNReal :=
  if q x = q y then 0 else c

theorem discreteRead_valid {A B : Type} [Nonempty A] (q : A → B) (c : ENNReal) :
    ExtendedPseudoMetric (Option A) none (liftDistance (discreteRead q c)) := by
  apply liftDistance_valid
  · intro x; simp [discreteRead]
  · intro x y; simp [discreteRead,eq_comm]
  · intro x y z
    by_cases hxy : q x = q y <;> by_cases hyz : q y = q z <;>
      by_cases hxz : q x = q z <;> simp_all [discreteRead]

def liftOperator {A : Type} (f : A → A) : Operator (Option A) none := ⟨Option.map f,rfl⟩

noncomputable def realGauge (q : ℝ → ℝ) : Option ℝ → Option ℝ → ENNReal :=
  liftDistance (fun x y => ENNReal.ofReal |q x-q y|)
theorem realGauge_valid (q : ℝ → ℝ) : ExtendedPseudoMetric (Option ℝ) none (realGauge q) := by
  apply liftDistance_valid
  · intro x; simp
  · intro x y; rw [abs_sub_comm]
  · intro x y z
    rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

theorem liftOperator_domain (f : ℝ → ℝ) : dom (liftOperator f) = Set.range some := by
  ext x; cases x <;> simp [dom,liftOperator]

def two : Set (Option Bool) := {some false, some true}
noncomputable def twoD : Option Bool → Option Bool → ENNReal := liftDistance (discreteRead id 1)
def swap : Operator (Option Bool) none := liftOperator Bool.not

theorem swap_example :
    ExtendedPseudoMetric (Option Bool) none twoD ∧
    two ⊆ dom swap ∧ swap.func '' two = two ∧
    activeComp (fun _ : Unit => twoD) swap two = univ ∧
    idComp (fun _ : Unit => twoD) swap two = ∅ ∧
    idComp (fun _ : Unit => twoD) (swap * swap) two = univ ∧
    activeComp (fun _ : Unit => twoD) (swap * swap) two = ∅ := by
  refine ⟨discreteRead_valid id 1,?_,?_,?_,?_,?_,?_⟩
  · intro x hx; rcases hx with rfl | hx; · simp [dom,swap,liftOperator]
    have : x = some true := hx; subst x; simp [dom,swap,liftOperator]
  · ext x; simp [two,swap,liftOperator,or_comm,eq_comm]
  all_goals
    ext i
    simp [activeComp,idComp,constComp,two,twoD,swap,liftOperator,
      operator_monoid,operator_compose,Function.comp_def,liftDistance,discreteRead]

def sevenU : Set (Option (Fin 6)) := {some 0,some 1}
def sevenPhi : Operator (Option (Fin 6)) none :=
  ⟨fun x => match x with
    | some 0 => some 2
    | some 1 => some 3
    | _ => none, rfl⟩
def sevenPsi : Operator (Option (Fin 6)) none :=
  ⟨fun x => match x with
    | some 2 => some 4
    | some 3 => some 5
    | _ => none, rfl⟩
noncomputable def sevenGauge (i : Bool) : Option (Fin 6) → Option (Fin 6) → ENNReal :=
  if i then liftDistance (discreteRead id 1)
  else liftDistance (discreteRead (fun x : Fin 6 => if x = 3 then 2 else x) 1)

theorem seven_example :
    (∀ i, ExtendedPseudoMetric (Option (Fin 6)) none (sevenGauge i)) ∧
    sevenU ⊆ dom (sevenPsi * sevenPhi) ∧
    false ∈ constComp sevenGauge sevenPhi sevenU ∧
    false ∉ constComp sevenGauge (sevenPsi * sevenPhi) sevenU ∧
    sevenGauge true (some 2) (some 3) = 1 := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i; cases i <;> apply discreteRead_valid
  · intro x hx; rcases hx with rfl | hx
    · norm_num [dom,operator_monoid,operator_compose,sevenPsi,sevenPhi] <;> decide
    · have : x = some 1 := hx; subst x
      norm_num [dom,operator_monoid,operator_compose,sevenPsi,sevenPhi] <;> decide
  all_goals norm_num [constComp,sevenU,sevenPhi,sevenPsi,sevenGauge,
    operator_monoid,operator_compose,Function.comp_def,liftDistance,discreteRead] <;> decide

noncomputable def infiniteGauge {I : Type} [DecidableEq I] (i k : I) :
    Option Bool → Option Bool → ENNReal :=
  liftDistance (discreteRead id (if k = i then ⊤ else 1))

theorem infinite_radius_example {I : Type} [DecidableEq I] (i j : I) :
    (∀ k, ExtendedPseudoMetric (Option Bool) none (infiniteGauge i k)) ∧
    two ⊆ dom (1 : Operator (Option Bool) none) ∧
    nullMatrix (infiniteGauge i) (1 : Operator (Option Bool) none) two j i = ⊤ ∧
    j ∉ constComp (infiniteGauge i) (1 : Operator (Option Bool) none) two := by
  refine ⟨fun k => discreteRead_valid id _,?_,?_,?_⟩
  · intro x hx; rcases hx with rfl | hx
    · simp [dom,operator_monoid,operator_identity]
    · have : x = some true := hx; subst x; simp [dom,operator_monoid,operator_identity]
  · apply top_unique; apply (le_uniform_iff _ _ _ _ _ _).mpr
    intro y hy x hx hxy
    have he : x = y := by
      rcases hx with rfl | hx <;> rcases hy with rfl | hy <;>
        simp_all [infiniteGauge,liftDistance,discreteRead]
    subst x
    exact (discreteRead_valid id _).dist_self _
  · intro h
    have hh := h (some false) (by simp [two]) (some true) (by simp [two])
    by_cases he : j = i <;>
      simp_all [infiniteGauge,liftDistance,discreteRead,operator_monoid,operator_identity]

def realTwo : Set (Option ℝ) := {some 0,some 1}
def affine : Operator (Option ℝ) none := liftOperator (fun x => 2*x-1)
noncomputable def absGauge : Unit → Option ℝ → Option ℝ → ENNReal := fun _ => realGauge abs

theorem affine_example :
    (∀ i, ExtendedPseudoMetric (Option ℝ) none (absGauge i)) ∧
    realTwo ⊆ dom (affine * affine) ∧
    fiber absGauge affine {()} (affine.func (some 0)) realTwo = realTwo ∧
    () ∈ constComp absGauge affine realTwo ∧
    fiber absGauge (affine * affine) {()} ((affine * affine).func (some 0)) realTwo = {some 0} ∧
    () ∈ activeComp absGauge (affine * affine) realTwo := by
  refine ⟨fun _ => realGauge_valid abs,?_,?_,?_,?_,?_⟩
  · intro x hx; rcases hx with rfl | hx
    · norm_num [dom,operator_monoid,operator_compose,affine,liftOperator] <;> simp
    · have : x = some 1 := hx; subst x
      norm_num [dom,operator_monoid,operator_compose,affine,liftOperator] <;> simp
  · ext x
    simp only [fiber,mem_setOf_eq,Set.mem_singleton_iff,forall_eq]
    constructor
    · exact And.left
    · intro hx; refine ⟨hx,?_⟩
      rcases hx with rfl | hx
      · norm_num [affine,liftOperator,absGauge,realGauge,liftDistance]
      · have : x = some 1 := hx; subst x
        norm_num [affine,liftOperator,absGauge,realGauge,liftDistance]
  · norm_num [constComp,realTwo,affine,liftOperator,absGauge,realGauge,liftDistance]
  · ext x
    simp only [fiber,mem_setOf_eq,Set.mem_singleton_iff,forall_eq]
    constructor
    · rintro ⟨hx,h⟩; rcases hx with rfl | hx
      · rfl
      · have : x = some 1 := hx; subst x
        norm_num [affine,liftOperator,absGauge,realGauge,liftDistance,
          operator_monoid,operator_compose] at h
    · rintro rfl
      norm_num [realTwo,affine,liftOperator,absGauge,realGauge,liftDistance,
        operator_monoid,operator_compose]
  · norm_num [activeComp,idComp,constComp,realTwo,affine,liftOperator,absGauge,realGauge,
      liftDistance,operator_monoid,operator_compose,Function.comp_def]

theorem point_constant_iteration {X : Type} {bot : X} (f : Operator X bot) (U : Set X)
    {c : X} (h : ∀ x ∈ U, f.func x = c) :
    (∀ x ∈ U, (f * f).func x = f.func c) ∧
    (f.func c ≠ bot → U ⊆ dom (f * f)) ∧
    (f.func c = bot → U ∩ dom (f * f) = ∅) := by
  have he : ∀ x ∈ U, (f * f).func x = f.func c := fun x hx => congrArg f.func (h x hx)
  refine ⟨he,?_,?_⟩
  · intro hc x hx; change (f*f).func x ≠ bot; rwa [he x hx]
  · intro hc; apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hd⟩; exact hd ((he x hx).trans hc)

theorem real_diameter_pair (a b : ℝ) :
    diameter (realGauge id) ({some a,some b} : Set (Option ℝ)) = ENNReal.ofReal |a-b| := by
  apply le_antisymm
  · apply iSup_le; intro x; apply iSup_le; intro hx
    apply iSup_le; intro y; apply iSup_le; intro hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy <;>
      simp_all [realGauge,liftDistance,abs_sub_comm]
  · exact le_diameter _ (x := some a) (y := some b) (by simp) (by simp)

theorem scale_counterexample :
    ({some (0 : ℝ)} : Set (Option ℝ)) ⊆ {some 0,some 1} ∧
    diameter (realGauge id) ({some (0 : ℝ)} : Set (Option ℝ)) < (1/2 : ENNReal) ∧
    (1/2 : ENNReal) ≤ diameter (realGauge id) ({some (0 : ℝ),some 1} : Set (Option ℝ)) := by
  have hs := real_diameter_pair 0 0
  have hp := real_diameter_pair 0 1
  norm_num at hs hp
  simp [hs,hp]

end Chapter3
