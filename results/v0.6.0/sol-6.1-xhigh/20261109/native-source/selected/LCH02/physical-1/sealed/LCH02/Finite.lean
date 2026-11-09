import LCH02.MatrixBounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

noncomputable section

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]

/-- Operators are listed in order of application. -/
def chain : List (Operator X bot) → Operator X bot
  | [] => 1
  | φ :: tail => chain tail * φ

theorem chain_eq_frozen (φs : List (Operator X bot)) :
    chain φs = OperatorChain φs.reverse := by
  rw [operator_chain_eq_prod]
  induction φs with
  | nil => rfl
  | cons φ tail ih => simp [chain, List.reverse_cons, List.prod_append, ih]

/-- m = 0 represents the textbook's U₁; m steps have already acted. -/
def actualDomain (φs : List (Operator X bot)) (U : Set X) (m : ℕ) : Set X :=
  operator_image (chain (φs.take m)) U

@[simp] theorem actualDomain_zero (φs : List (Operator X bot)) (U : Set X) :
    actualDomain φs U 0 = U := by
  change id '' U = U
  exact Set.image_id U

@[simp] theorem actualDomain_succ (φ : Operator X bot) (tail : List (Operator X bot))
    (U : Set X) (m : ℕ) :
    actualDomain (φ :: tail) U (m + 1) = actualDomain tail (operator_image φ U) m := by
  change ((chain (tail.take m)).func ∘ φ.func) '' U =
    (chain (tail.take m)).func '' (φ.func '' U)
  exact (Set.image_image (chain (tail.take m)).func φ.func U).symm

theorem actualDomain_legal (φs : List (Operator X bot)) {U : Set X}
    (hU : U ⊆ dom (chain φs)) (m : ℕ) (hm : m < φs.length) :
    actualDomain φs U m ⊆ dom φs[m] := by
  induction φs generalizing U m with
  | nil => simp at hm
  | cons φ tail ih =>
      have hparts := composition_domains φ (chain tail) hU
      cases m with
      | zero => simpa using hparts.1
      | succ m =>
          simpa using ih hparts.2 m (Nat.lt_of_succ_lt_succ hm)

/-- Only single-step assertions appear here, on the exact recursive image domains. -/
def Stepwise (P : Operator X bot → Set X → BoundMatrix I → Prop) :
    List (Operator X bot × BoundMatrix I) → Set X → Prop
  | [], _ => True
  | s :: tail, U => P s.1 U s.2 ∧ Stepwise P tail (operator_image s.1 U)

omit [Fintype I] [DecidableEq I] in
theorem stepwise_iff_actualDomains
    (P : Operator X bot → Set X → BoundMatrix I → Prop)
    (steps : List (Operator X bot × BoundMatrix I)) (U : Set X) :
    Stepwise P steps U ↔ ∀ m (hm : m < steps.length),
      P steps[m].1 (actualDomain (steps.map Prod.fst) U m) steps[m].2 := by
  induction steps generalizing U with
  | nil => simp [Stepwise]
  | cons s tail ih =>
      constructor
      · intro hs m hm
        cases m with
        | zero => simpa using hs.1
        | succ m =>
            simpa using (ih (operator_image s.1 U)).mp hs.2 m (Nat.lt_of_succ_lt_succ hm)
      · intro h
        refine ⟨?_, (ih (operator_image s.1 U)).mpr ?_⟩
        · simpa using h 0 (by simp)
        · intro m hm
          simpa using h (m + 1) (Nat.succ_lt_succ hm)

theorem finite_lip (d : I → X → X → ENNReal)
    (steps : List (Operator X bot × BoundMatrix I)) {U : Set X}
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hsteps : Stepwise (LipOn d) steps U) :
    LipOn d (chain (steps.map Prod.fst)) U (matrixProduct (steps.map Prod.snd)) := by
  induction steps generalizing U with
  | nil => exact identity_lip d hU
  | cons s tail ih =>
      rcases s with ⟨φ, L⟩
      have htail := (composition_domains φ (chain (tail.map Prod.fst)) hU).2
      have h := lip_comp d φ (chain (tail.map Prod.fst)) hU hsteps.1
        (ih htail hsteps.2)
      simpa [chain] using h

theorem finite_coLip (d : I → X → X → ENNReal)
    (steps : List (Operator X bot × BoundMatrix I)) {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hsteps : Stepwise (CoLipOn d) steps U) :
    CoLipOn d (chain (steps.map Prod.fst)) U (matrixProduct (steps.map Prod.snd)) := by
  induction steps generalizing U with
  | nil => exact identity_coLip d hne hU
  | cons s tail ih =>
      rcases s with ⟨φ, K⟩
      have htail := (composition_domains φ (chain (tail.map Prod.fst)) hU).2
      have h := coLip_comp d φ (chain (tail.map Prod.fst)) hU hsteps.1
        (ih (hne.image φ.func) htail hsteps.2)
      simpa [chain] using h

theorem finite_coLip_positive (d : I → X → X → ENNReal)
    (steps : List (Operator X bot × BoundMatrix I)) (hpos : steps ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hsteps : Stepwise (CoLipOn d) steps U) :
    CoLipOn d (chain (steps.map Prod.fst)) U (matrixProduct (steps.map Prod.snd)) := by
  cases steps with
  | nil => exact False.elim (hpos rfl)
  | cons s tail => exact finite_coLip d (s :: tail) hsteps.1.1 hU hsteps

end
end LCH02
