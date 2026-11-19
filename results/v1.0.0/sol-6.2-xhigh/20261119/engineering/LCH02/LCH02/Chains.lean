import LCH02.Bounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X}

/-- The list of operators is in application order. -/
def chain (steps : List (Operator X bot)) : Operator X bot :=
  OperatorChain steps.reverse

@[simp] theorem chain_nil : chain ([] : List (Operator X bot)) = 1 := rfl

@[simp] theorem chain_single (φ : Operator X bot) : chain [φ] = φ := by
  simp [chain, operator_chain_eq_prod]

theorem chain_append (steps rest : List (Operator X bot)) :
    chain (steps ++ rest) = chain rest * chain steps := by
  simp [chain, operator_chain_eq_prod, List.reverse_append, List.prod_append]

theorem chain_cons (φ : Operator X bot) (rest : List (Operator X bot)) :
    chain (φ :: rest) = chain rest * φ := by
  simpa only [List.singleton_append, chain_single] using chain_append [φ] rest

/-- After `m` steps, the next step receives the image of the initial set
under the first `m` operators. -/
def stageDomain (steps : List (Operator X bot)) (U : Set X) (m : ℕ) : Set X :=
  operator_image (chain (steps.take m)) U

@[simp] theorem stageDomain_zero (steps : List (Operator X bot)) (U : Set X) :
    stageDomain steps U 0 = U := by
  change id '' U = U
  exact Set.image_id U

theorem stageDomain_length (steps : List (Operator X bot)) (U : Set X) :
    stageDomain steps U steps.length = operator_image (chain steps) U := by
  simp [stageDomain]

theorem stageDomain_cons (φ : Operator X bot) (rest : List (Operator X bot))
    (U : Set X) (m : ℕ) :
    stageDomain (φ :: rest) U (m + 1) = stageDomain rest (operator_image φ U) m := by
  simp only [stageDomain, List.take_succ_cons, chain_cons, image_mul]

theorem stageDomain_next (steps : List (Operator X bot)) (U : Set X)
    (m : Fin steps.length) :
    stageDomain steps U (m.val + 1) =
      operator_image steps[m.val] (stageDomain steps U m.val) := by
  simp only [stageDomain, List.take_succ_eq_append_getElem m.isLt,
    chain_append, chain_single, image_mul]

theorem stageDomain_subset_step_dom {steps : List (Operator X bot)} {U : Set X}
    (hU : U ⊆ dom (chain steps)) (m : Fin steps.length) :
    stageDomain steps U m.val ⊆ dom steps[m.val] := by
  induction steps generalizing U with
  | nil => exact Fin.elim0 m
  | cons φ rest ih =>
      rw [chain_cons] at hU
      refine Fin.cases ?_ (fun k => ?_) m
      · simpa using fun x hx => (mem_dom_mul.mp (hU (a := x) hx)).1
      · simpa [stageDomain_cons] using ih (image_subset_dom_of_mul hU) k

variable [Fintype I] {g : Gauge X I bot} {U : Set X}

private theorem chain_bound
    (Bound : Operator X bot → Set X → Coefficients I → Prop)
    (comp : ∀ {φ ψ U A B}, U ⊆ dom (ψ * φ) →
      Bound φ U A → Bound ψ (operator_image φ U) B → Bound (ψ * φ) U (B * A))
    {first : Operator X bot × Coefficients I} {rest : List (Operator X bot × Coefficients I)}
    (hU : U ⊆ dom (chain ((first :: rest).map Prod.fst)))
    (hstep : ∀ m : Fin (first :: rest).length,
      Bound (first :: rest)[m.val].1
        (stageDomain ((first :: rest).map Prod.fst) U m.val) (first :: rest)[m.val].2) :
    Bound (chain ((first :: rest).map Prod.fst)) U
      (matrixProduct ((first :: rest).map Prod.snd)) := by
  induction rest generalizing first U with
  | nil =>
      simpa using hstep (0 : Fin 1)
  | cons next rest ih =>
      have hfirst : Bound first.1 U first.2 := by
        simpa using hstep ⟨0, by simp⟩
      have hcomp : U ⊆ dom (chain ((next :: rest).map Prod.fst) * first.1) := by
        simpa only [List.map_cons, chain_cons] using hU
      have htail (m : Fin (next :: rest).length) :
          Bound (next :: rest)[m.val].1
            (stageDomain ((next :: rest).map Prod.fst) (operator_image first.1 U) m.val)
            (next :: rest)[m.val].2 := by
        simpa only [Fin.val_succ, List.getElem_cons_succ, List.map_cons, stageDomain_cons]
          using hstep m.succ
      have hrest := ih (image_subset_dom_of_mul hcomp) htail
      simpa only [List.map_cons, chain_cons, matrixProduct_cons] using comp hcomp hfirst hrest

theorem chain_lip
    {first : Operator X bot × Coefficients I} {rest : List (Operator X bot × Coefficients I)}
    (hU : U ⊆ dom (chain ((first :: rest).map Prod.fst)))
    (hstep : ∀ m : Fin (first :: rest).length,
      LipOn g (first :: rest)[m.val].1
        (stageDomain ((first :: rest).map Prod.fst) U m.val) (first :: rest)[m.val].2) :
    LipOn g (chain ((first :: rest).map Prod.fst)) U
      (matrixProduct ((first :: rest).map Prod.snd)) :=
  chain_bound (LipOn g) lip_comp hU hstep

theorem chain_coLip
    {first : Operator X bot × Coefficients I} {rest : List (Operator X bot × Coefficients I)}
    (hU : U ⊆ dom (chain ((first :: rest).map Prod.fst)))
    (hstep : ∀ m : Fin (first :: rest).length,
      CoLipOn g (first :: rest)[m.val].1
        (stageDomain ((first :: rest).map Prod.fst) U m.val) (first :: rest)[m.val].2) :
    CoLipOn g (chain ((first :: rest).map Prod.fst)) U
      (matrixProduct ((first :: rest).map Prod.snd)) :=
  chain_bound (CoLipOn g) coLip_comp hU hstep

end LCH02
