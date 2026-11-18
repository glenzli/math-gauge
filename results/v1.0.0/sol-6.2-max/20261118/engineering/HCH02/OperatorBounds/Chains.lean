import OperatorBounds.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators ENNReal

variable {X I : Type} {bot : X} {n : ℕ}

noncomputable def matrixOne : BoundMatrix I := by
  classical
  exact fun i j => if i = j then 1 else 0

theorem display_one [DecidableEq I] :
    display (matrixOne : BoundMatrix I) = 1 := by
  ext j i
  simp [display, matrixOne, Matrix.one_apply, eq_comm]

noncomputable def matrixProduct [Fintype I] : List (BoundMatrix I) → BoundMatrix I
  | [] => matrixOne
  | M :: rest => matrixMul (matrixProduct rest) M

@[simp] theorem matrixProduct_nil [Fintype I] :
    matrixProduct ([] : List (BoundMatrix I)) = matrixOne := rfl

@[simp] theorem matrixProduct_singleton [Fintype I] (M : BoundMatrix I) :
    matrixProduct [M] = M := by
  classical
  apply display.injective
  simp [matrixProduct, display_mul, display_one]

/-- The list is in execution order, with the first operator applied first. -/
def orderedComposition (ops : List (Operator X bot)) : Operator X bot :=
  OperatorChain ops.reverse

@[simp] theorem orderedComposition_nil :
    orderedComposition ([] : List (Operator X bot)) = identityOp := rfl

private theorem operatorChain_append_singleton (ops : List (Operator X bot))
    (φ : Operator X bot) :
    OperatorChain (ops ++ [φ]) = composeOp (OperatorChain ops) φ := by
  induction ops with
  | nil => rfl
  | cons ψ ops ih =>
    ext x
    exact congrArg (fun F : Operator X bot => ψ.func (F.func x)) ih

@[simp] theorem orderedComposition_cons (φ : Operator X bot) (ops : List (Operator X bot)) :
    orderedComposition (φ :: ops) = composeOp (orderedComposition ops) φ := by
  rw [orderedComposition, List.reverse_cons, operatorChain_append_singleton]
  rfl

def imageAlong (U : Set X) (ops : List (Operator X bot)) : Set X :=
  ops.foldl (fun V φ => operator_image φ V) U

theorem imageAlong_eq (U : Set X) (ops : List (Operator X bot)) :
    imageAlong U ops = operator_image (orderedComposition ops) U := by
  induction ops generalizing U with
  | nil => simp [imageAlong, orderedComposition, OperatorChain, operator_image]
  | cons φ ops ih =>
    change imageAlong (operator_image φ U) ops = _
    rw [ih, orderedComposition_cons]
    exact Set.image_image (orderedComposition ops).func φ.func U

/-- actualInput U ops m is the image after m applications. Step m uses zero-based indexing. -/
def actualInput (U : Set X) (ops : Fin n → Operator X bot) (m : ℕ) : Set X :=
  imageAlong U ((List.ofFn ops).take m)

@[simp] theorem actualInput_zero (U : Set X) (ops : Fin n → Operator X bot) :
    actualInput U ops 0 = U := rfl

theorem actualInput_succ (U : Set X) (ops : Fin n → Operator X bot) (m : Fin n) :
    actualInput U ops (m.val + 1) = operator_image (ops m) (actualInput U ops m) := by
  unfold actualInput
  rw [List.take_succ_eq_append_getElem (by simp)]
  simp [imageAlong, List.foldl_append, List.getElem_ofFn]

theorem actualInput_full (U : Set X) (ops : Fin n → Operator X bot) :
    actualInput U ops n = operator_image (orderedComposition (List.ofFn ops)) U := by
  have h : (List.ofFn ops).length ≤ n := by simp
  rw [actualInput, List.take_of_length_le h, imageAlong_eq]

private theorem actualInput_shift (U : Set X) (ops : Fin (n + 1) → Operator X bot)
    (m : ℕ) :
    actualInput U ops (m + 1) =
      actualInput (operator_image (ops 0) U) (fun k : Fin n => ops k.succ) m := by
  rw [actualInput, List.ofFn_succ]
  rfl

theorem actualInput_subset_dom (U : Set X) (ops : Fin n → Operator X bot)
    (hU : U ⊆ dom (orderedComposition (List.ofFn ops))) (m : Fin n) :
    actualInput U ops m ⊆ dom (ops m) := by
  induction n generalizing U with
  | zero => exact Fin.elim0 m
  | succ n ih =>
    rw [List.ofFn_succ, orderedComposition_cons] at hU
    obtain ⟨hfirst, hrest⟩ := compose_domains hU
    refine Fin.cases hfirst (fun k => ?_) m
    rw [Fin.val_succ, actualInput_shift]
    exact ih _ _ hrest k

def Stepwise (valid : Operator X bot → Set X → BoundMatrix I → Prop)
    (U : Set X) (ops : Fin n → Operator X bot) (M : Fin n → BoundMatrix I) : Prop :=
  ∀ m, valid (ops m) (actualInput U ops m) (M m)

theorem stepwise_succ (valid : Operator X bot → Set X → BoundMatrix I → Prop)
    (U : Set X) (ops : Fin (n + 1) → Operator X bot) (M : Fin (n + 1) → BoundMatrix I) :
    Stepwise valid U ops M ↔ valid (ops 0) U (M 0) ∧
      Stepwise valid (operator_image (ops 0) U)
        (fun k : Fin n => ops k.succ) (fun k => M k.succ) := by
  simp only [Stepwise, Fin.forall_fin_succ, Fin.val_zero, actualInput_zero,
    Fin.val_succ, actualInput_shift]

variable [Fintype I] {d : I → X → X → ℝ≥0∞} {U : Set X}

theorem weightedDistance_one (d : I → X → X → ℝ≥0∞) (x y : X) (j : I) :
    weightedDistance d matrixOne x y j = d j x y := by
  classical
  simp [weightedDistance, matrixOne, ite_mul]

theorem identity_lip (hU : U ⊆ dom (identityOp : Operator X bot)) :
    matrixOne ∈ lipOn d (identityOp (bot := bot)) U := by
  refine ⟨hU, fun x y _ _ j => ?_⟩
  exact (weightedDistance_one d x y j).ge

theorem identity_coLip (hU : U ⊆ dom (identityOp : Operator X bot)) (hNE : U.Nonempty) :
    matrixOne ∈ coLipOn d (identityOp (bot := bot)) U := by
  refine ⟨hNE, hU, fun x y _ _ j => ?_⟩
  exact (weightedDistance_one d x y j).le

theorem empty_chain_bounds (hU : U ⊆ dom (identityOp : Operator X bot)) (hNE : U.Nonempty) :
    matrixProduct [] ∈ lipOn d (orderedComposition (bot := bot) []) U ∧
      matrixProduct [] ∈ coLipOn d (orderedComposition (bot := bot) []) U :=
  ⟨identity_lip hU, identity_coLip hU hNE⟩

private theorem lip_chain_all (ops : Fin n → Operator X bot) (L : Fin n → BoundMatrix I)
    (hU : U ⊆ dom (orderedComposition (List.ofFn ops)))
    (hL : Stepwise (fun φ V M => M ∈ lipOn d φ V) U ops L) :
    matrixProduct (List.ofFn L) ∈ lipOn d (orderedComposition (List.ofFn ops)) U := by
  induction n generalizing U with
  | zero =>
    simp only [List.ofFn_zero] at hU ⊢
    exact identity_lip hU
  | succ n ih =>
    simp only [List.ofFn_succ, orderedComposition_cons] at hU ⊢
    obtain ⟨hfirst, hrest⟩ := (stepwise_succ _ _ _ _).mp hL
    exact lip_compose hU hfirst (ih _ _ (compose_domains hU).2 hrest)

theorem lip_chain (ops : Fin (n + 1) → Operator X bot) (L : Fin (n + 1) → BoundMatrix I)
    (hU : U ⊆ dom (orderedComposition (List.ofFn ops)))
    (hL : Stepwise (fun φ V M => M ∈ lipOn d φ V) U ops L) :
    matrixProduct (List.ofFn L) ∈ lipOn d (orderedComposition (List.ofFn ops)) U :=
  lip_chain_all ops L hU hL

private theorem coLip_chain_of_nonempty (ops : Fin n → Operator X bot) (K : Fin n → BoundMatrix I)
    (hU : U ⊆ dom (orderedComposition (List.ofFn ops))) (hNE : U.Nonempty)
    (hK : Stepwise (fun φ V M => M ∈ coLipOn d φ V) U ops K) :
    matrixProduct (List.ofFn K) ∈ coLipOn d (orderedComposition (List.ofFn ops)) U := by
  induction n generalizing U with
  | zero =>
    simp only [List.ofFn_zero] at hU ⊢
    exact identity_coLip hU hNE
  | succ n ih =>
    simp only [List.ofFn_succ, orderedComposition_cons] at hU ⊢
    obtain ⟨hfirst, hrest⟩ := (stepwise_succ _ _ _ _).mp hK
    exact coLip_compose hU hfirst
      (ih _ _ (compose_domains hU).2 (hNE.image (ops 0).func) hrest)

theorem coLip_chain (ops : Fin (n + 1) → Operator X bot) (K : Fin (n + 1) → BoundMatrix I)
    (hU : U ⊆ dom (orderedComposition (List.ofFn ops)))
    (hK : Stepwise (fun φ V M => M ∈ coLipOn d φ V) U ops K) :
    matrixProduct (List.ofFn K) ∈ coLipOn d (orderedComposition (List.ofFn ops)) U :=
  coLip_chain_of_nonempty ops K hU ((stepwise_succ _ _ _ _).mp hK).1.1 hK

end HCH02
