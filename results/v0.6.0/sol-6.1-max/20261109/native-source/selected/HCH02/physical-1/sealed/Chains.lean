import Bounds

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical ENNReal
noncomputable section
namespace HCH02

variable {X I : Type} {bot : X} [Fintype I]

/-- Lists are in application order: the head acts first. -/
def prodMat : List (Mat I) → Mat I
  | [] => unit
  | A :: As => mmul (prodMat As) A

@[simp] theorem prodMat_nil : prodMat ([] : List (Mat I)) = unit := rfl
@[simp] theorem prodMat_single (A : Mat I) : prodMat [A] = A := mmul_unit_left A

theorem prodMat_append (As Bs : List (Mat I)) :
    prodMat (As ++ Bs) = mmul (prodMat Bs) (prodMat As) := by
  induction As with
  | nil => simp [mmul_unit_right]
  | cons A As ih =>
    simp only [List.cons_append, prodMat, ih, mmul_assoc]

/-- Only single-step data; no composite estimate is stored. -/
structure Step (X : Type) (bot : X) (I : Type) where
  op : Operator X bot
  upper : Mat I
  lower : Mat I

def chain : List (Step X bot I) → Operator X bot
  | [] => ident
  | s :: ss => comp (chain ss) s.op

theorem chain_single (s : Step X bot I) : chain [s] = s.op := by
  ext x
  rfl

theorem chain_append (ss ts : List (Step X bot I)) :
    chain (ss ++ ts) = comp (chain ts) (chain ss) := by
  induction ss with
  | nil => ext x; rfl
  | cons s ss ih =>
    simp only [List.cons_append, chain, ih]
    ext x
    rfl

def actualImage : List (Step X bot I) → Set X → Set X
  | [], U => U
  | s :: ss, U => actualImage ss (s.op.func '' U)

def Safe : List (Step X bot I) → Set X → Prop
  | [], U => U ⊆ dom (ident : Operator X bot)
  | s :: ss, U => U ⊆ dom s.op ∧ Safe ss (s.op.func '' U)

def StepLip (d : I → X → X → ℝ≥0∞) : List (Step X bot I) → Set X → Prop
  | [], _ => True
  | s :: ss, U => s.upper ∈ Lip d s.op U ∧ StepLip d ss (s.op.func '' U)

def StepCoLip (d : I → X → X → ℝ≥0∞) : List (Step X bot I) → Set X → Prop
  | [], _ => True
  | s :: ss, U => s.lower ∈ CoLip d s.op U ∧ StepCoLip d ss (s.op.func '' U)

theorem safe_iff (ss : List (Step X bot I)) (U : Set X) :
    Safe ss U ↔ U ⊆ dom (chain ss) := by
  induction ss generalizing U with
  | nil => rfl
  | cons s ss ih =>
    rw [Safe, chain, dom_comp]
    constructor
    · rintro ⟨hhead, htail⟩ x hx
      exact ⟨hhead hx, (ih _).mp htail ⟨x, hx, rfl⟩⟩
    · intro h
      refine ⟨fun x hx => (h hx).1, (ih _).mpr ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact (h hx).2

theorem chain_image (ss : List (Step X bot I)) (U : Set X) :
    (chain ss).func '' U = actualImage ss U := by
  induction ss generalizing U with
  | nil => simp [chain, actualImage, ident]
  | cons s ss ih =>
    simpa only [chain, comp, Function.comp_def, Set.image_image, actualImage] using
      ih (s.op.func '' U)

/-- The input at every textbook step, expressed by its preceding prefix. -/
theorem actual_step_domain (pre : List (Step X bot I)) (s : Step X bot I)
    (tail : List (Step X bot I)) (U : Set X)
    (hU : U ⊆ dom (chain (pre ++ s :: tail))) :
    actualImage pre U ⊆ dom s.op := by
  rw [← chain_image]
  rintro _ ⟨x, hx, rfl⟩
  have ht := hU hx
  rw [chain_append, dom_comp] at ht
  have hs := ht.2
  change (chain pre).func x ∈ dom (comp (chain tail) s.op) at hs
  rw [dom_comp] at hs
  exact hs.1

/-- Converts primitive bounds at every actual input into recursive chain data. -/
theorem stepLip_iff (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X bot I)) (U : Set X) :
    StepLip d ss U ↔ ∀ pre s tail, ss = pre ++ s :: tail →
      s.upper ∈ Lip d s.op (actualImage pre U) := by
  induction ss generalizing U with
  | nil =>
    constructor
    · intro _ pre s tail heq
      cases pre <;> simp at heq
    · intro _
      trivial
  | cons a ss ih =>
    constructor
    · intro h pre s tail heq
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact h.1
      | cons b pre =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, heq⟩
        exact (ih _).mp h.2 pre s tail heq
    · intro h
      refine ⟨h [] a ss rfl, (ih _).mpr ?_⟩
      intro pre s tail heq
      exact h (a :: pre) s tail (by simp only [List.cons_append, heq])

theorem stepCoLip_iff (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X bot I)) (U : Set X) :
    StepCoLip d ss U ↔ ∀ pre s tail, ss = pre ++ s :: tail →
      s.lower ∈ CoLip d s.op (actualImage pre U) := by
  induction ss generalizing U with
  | nil =>
    constructor
    · intro _ pre s tail heq
      cases pre <;> simp at heq
    · intro _
      trivial
  | cons a ss ih =>
    constructor
    · intro h pre s tail heq
      cases pre with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, rfl⟩
        exact h.1
      | cons b pre =>
        simp only [List.cons_append, List.cons.injEq] at heq
        rcases heq with ⟨rfl, heq⟩
        exact (ih _).mp h.2 pre s tail heq
    · intro h
      refine ⟨h [] a ss rfl, (ih _).mpr ?_⟩
      intro pre s tail heq
      exact h (a :: pre) s tail (by simp only [List.cons_append, heq])

theorem lip_unit (d : I → X → X → ℝ≥0∞) (U : Set X)
    (hU : U ⊆ dom (ident : Operator X bot)) :
    unit ∈ Lip d (ident : Operator X bot) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simp [unit, ident]

theorem colip_unit (d : I → X → X → ℝ≥0∞) (U : Set X)
    (hne : U.Nonempty) (hU : U ⊆ dom (ident : Operator X bot)) :
    unit ∈ CoLip d (ident : Operator X bot) U := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  simp [unit, ident]

theorem lip_chain (d : I → X → X → ℝ≥0∞) (ss : List (Step X bot I)) (U : Set X)
    (hU : U ⊆ dom (chain ss)) (hs : StepLip d ss U) :
    prodMat (ss.map Step.upper) ∈ Lip d (chain ss) U := by
  induction ss generalizing U with
  | nil => exact lip_unit d U hU
  | cons s ss ih =>
    have htail : s.op.func '' U ⊆ dom (chain ss) := by
      rintro _ ⟨x, hx, rfl⟩
      have ht : x ∈ dom s.op ∩ s.op.func ⁻¹' dom (chain ss) := by
        simpa only [chain, dom_comp] using hU hx
      exact ht.2
    exact lip_comp hU hs.1 (ih _ htail hs.2)

theorem colip_chain (d : I → X → X → ℝ≥0∞) (ss : List (Step X bot I)) (U : Set X)
    (hne : U.Nonempty) (hU : U ⊆ dom (chain ss)) (hs : StepCoLip d ss U) :
    prodMat (ss.map Step.lower) ∈ CoLip d (chain ss) U := by
  induction ss generalizing U with
  | nil => exact colip_unit d U hne hU
  | cons s ss ih =>
    have htail : s.op.func '' U ⊆ dom (chain ss) := by
      rintro _ ⟨x, hx, rfl⟩
      have ht : x ∈ dom s.op ∩ s.op.func ⁻¹' dom (chain ss) := by
        simpa only [chain, dom_comp] using hU hx
      exact ht.2
    exact colip_comp hU hs.1 (ih _ (hne.image _) htail hs.2)

theorem positive_length_colip_chain (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X bot I)) (U : Set X) (hn : ss ≠ [])
    (hU : U ⊆ dom (chain ss)) (hs : StepCoLip d ss U) :
    prodMat (ss.map Step.lower) ∈ CoLip d (chain ss) U := by
  apply colip_chain d ss U ?_ hU hs
  cases ss with
  | nil => exact (hn rfl).elim
  | cons s ss => exact hs.1.1

/-- Recursive tuples of all intermediate indices, with no edge restriction. -/
def Route (I : Type) : Nat → Type
  | 0 => PUnit
  | n + 1 => I × Route I n

theorem route_zero_unique (r : Route I 0) : r = PUnit.unit := by cases r; rfl

instance routeFintype (n : Nat) : Fintype (Route I n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (I × Route I n))

/-- Explicit correspondence with the textbook's n intermediate indices. -/
def routeEquiv : (n : Nat) → Route I n ≃ (Fin n → I)
  | 0 =>
    { toFun := fun _ => Fin.elim0
      invFun := fun _ => PUnit.unit
      left_inv := by intro r; cases r; rfl
      right_inv := fun _ => funext fun k => Fin.elim0 k }
  | n + 1 =>
    { toFun := fun r => Fin.cons r.1 (routeEquiv n r.2)
      invFun := fun f => (f 0, (routeEquiv n).symm (Fin.tail f))
      left_inv := by
        intro r
        rcases r with ⟨k, r⟩
        simp
      right_inv := by
        intro f
        simp }

def weight : (As : List (Mat I)) → I → I → Route I (As.length - 1) → ℝ≥0∞
  | [], i, j, _ => unit i j
  | [A], i, j, _ => A i j
  | A :: B :: As, i, j, r => weight (B :: As) r.1 j r.2 * A i r.1

def AllPositive : (As : List (Mat I)) → I → I → Route I (As.length - 1) → Prop
  | [], _, _, _ => True
  | [A], i, j, _ => 0 < A i j
  | A :: B :: As, i, j, r => 0 < A i r.1 ∧ AllPositive (B :: As) r.1 j r.2

def HasZero : (As : List (Mat I)) → I → I → Route I (As.length - 1) → Prop
  | [], _, _, _ => False
  | [A], i, j, _ => A i j = 0
  | A :: B :: As, i, j, r => A i r.1 = 0 ∨ HasZero (B :: As) r.1 j r.2

theorem weight_zero (As : List (Mat I)) (hn : As ≠ []) (i j : I)
    (r : Route I (As.length - 1)) : weight As i j r = 0 ↔ HasZero As i j r := by
  induction As generalizing i j with
  | nil => exact (hn rfl).elim
  | cons A As ih =>
    cases As with
    | nil => rfl
    | cons B Bs =>
      rcases r with ⟨k, r⟩
      simp only [weight, HasZero, mul_eq_zero, ih (by simp)]
      exact or_comm

theorem weight_positive (As : List (Mat I)) (hn : As ≠ []) (i j : I)
    (r : Route I (As.length - 1)) : 0 < weight As i j r ↔ AllPositive As i j r := by
  induction As generalizing i j with
  | nil => exact (hn rfl).elim
  | cons A As ih =>
    cases As with
    | nil => rfl
    | cons B Bs =>
      rcases r with ⟨k, r⟩
      simp only [weight, AllPositive, ENNReal.mul_pos_iff, ih (by simp)]
      exact and_comm

theorem path_expansion (As : List (Mat I)) (hn : As ≠ []) (i j : I) :
    prodMat As i j = ∑ r : Route I (As.length - 1), weight As i j r := by
  induction As generalizing i j with
  | nil => exact (hn rfl).elim
  | cons A As ih =>
    cases As with
    | nil => simp [weight, prodMat_single, Route]
    | cons B Bs =>
      change (∑ k, prodMat (B :: Bs) k j * A i k) =
        ∑ r : I × Route I Bs.length, weight (B :: Bs) r.1 j r.2 * A i r.1
      simp_rw [ih (by simp), Finset.sum_mul]
      exact (Fintype.sum_prod_type
        (fun r : I × Route I Bs.length => weight (B :: Bs) r.1 j r.2 * A i r.1)).symm

theorem product_zero_iff (As : List (Mat I)) (hn : As ≠ []) (i j : I) :
    prodMat As i j = 0 ↔ ∀ r, HasZero As i j r := by
  rw [path_expansion As hn i j]
  simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const, weight_zero As hn]

theorem product_positive_iff (As : List (Mat I)) (hn : As ≠ []) (i j : I) :
    0 < prodMat As i j ↔ ∃ r, AllPositive As i j r := by
  rw [path_expansion As hn i j]
  simp only [Finset.sum_pos_iff, Finset.mem_univ, true_and, weight_positive As hn]

theorem certified_lip_zero (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X bot I)) (U : Set X) (hn : ss ≠ [])
    (hU : U ⊆ dom (chain ss)) (hL : StepLip d ss U) (hK : StepCoLip d ss U)
    (i j : I) :
    prodMat (ss.map Step.upper) i j = 0 ↔ ∀ r, HasZero (ss.map Step.upper) i j r := by
  exact product_zero_iff _ (by simpa using hn) i j

theorem certified_colip_positive (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X bot I)) (U : Set X) (hn : ss ≠ [])
    (hU : U ⊆ dom (chain ss)) (hL : StepLip d ss U) (hK : StepCoLip d ss U)
    (i j : I) :
    0 < prodMat (ss.map Step.lower) i j ↔ ∃ r, AllPositive (ss.map Step.lower) i j r := by
  exact product_positive_iff _ (by simpa using hn) i j

end HCH02
