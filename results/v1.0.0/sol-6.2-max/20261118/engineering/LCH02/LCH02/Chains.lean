import LCH02.MatrixBounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X}

/-- Operators are listed in the order in which they act. -/
def chain (ops : List (Operator X bot)) : Operator X bot :=
  OperatorChain ops.reverse

@[simp] theorem chain_nil : chain ([] : List (Operator X bot)) = 1 := rfl

theorem chain_cons (f : Operator X bot) (ops : List (Operator X bot)) :
    chain (f :: ops) = chain ops * f := by
  simp [chain, operator_chain_eq_prod, List.prod_append]

@[simp] theorem chain_singleton (f : Operator X bot) : chain [f] = f := by
  rw [chain_cons, chain_nil, one_mul]

/-- After `m` steps this is the input domain for step `m + 1` in the text. -/
def prefixDomain (ops : List (Operator X bot)) (U : Set X) (m : ℕ) : Set X :=
  operator_image (chain (ops.take m)) U

@[simp] theorem prefixDomain_zero (ops : List (Operator X bot)) (U : Set X) :
    prefixDomain ops U 0 = U :=
  Set.image_id U

private theorem prefixDomain_cons_succ
    (f : Operator X bot) (ops : List (Operator X bot)) (U : Set X) (m : ℕ) :
    prefixDomain (f :: ops) U (m + 1) = prefixDomain ops (operator_image f U) m := by
  unfold prefixDomain
  rw [List.take_succ_cons, chain_cons]
  exact (Set.image_image (chain (ops.take m)).func f.func U).symm

theorem prefixDomain_step (ops : List (Operator X bot)) (U : Set X) (m : Fin ops.length) :
    prefixDomain ops U (m.val + 1) = operator_image (ops.get m) (prefixDomain ops U m.val) := by
  induction ops generalizing U with
  | nil => exact m.elim0
  | cons f ops ih =>
    cases m using Fin.cases with
    | zero => simp [prefixDomain_cons_succ]
    | succ k =>
      simpa only [Fin.val_succ, List.get_cons_succ', prefixDomain_cons_succ] using
        ih (operator_image f U) k

theorem prefixDomain_subset (ops : List (Operator X bot)) {U : Set X}
    (hU : U ⊆ dom (chain ops)) (m : Fin ops.length) :
    prefixDomain ops U m.val ⊆ dom (ops.get m) := by
  induction ops generalizing U with
  | nil => exact m.elim0
  | cons f ops ih =>
    rw [chain_cons] at hU
    obtain ⟨hfirst, hrest⟩ := composed_domains hU
    cases m using Fin.cases with
    | zero => simpa only [Fin.val_zero, List.get_cons_zero, prefixDomain_zero] using hfirst
    | succ k =>
      simpa only [Fin.val_succ, List.get_cons_succ', prefixDomain_cons_succ] using ih hrest k

variable [Fintype I]

private theorem chain_bounds
    (Valid : Operator X bot → Set X → BoundMatrix I → Prop)
    (compose : ∀ {f g : Operator X bot} {U : Set X} {A B : BoundMatrix I},
      U ⊆ dom (g * f) → Valid f U A → Valid g (operator_image f U) B →
      Valid (g * f) U (B * A))
    (steps : List (Operator X bot × BoundMatrix I)) (hne : steps ≠ []) (U : Set X)
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hstep : ∀ m : Fin steps.length, Valid (steps.get m).1
      (prefixDomain (steps.map Prod.fst) U m.val) (steps.get m).2) :
    Valid (chain (steps.map Prod.fst)) U (matrixProduct (steps.map Prod.snd)) := by
  induction steps generalizing U with
  | nil => exact (hne rfl).elim
  | cons s steps ih =>
    have hfirst : Valid s.1 U s.2 := by
      simpa only [Fin.val_zero, List.get_cons_zero, prefixDomain_zero] using
        hstep (0 : Fin (s :: steps).length)
    cases steps with
    | nil => simpa using hfirst
    | cons t rest =>
      have hcomp : U ⊆ dom (chain ((t :: rest).map Prod.fst) * s.1) := by
        simpa only [List.map_cons, chain_cons] using hU
      have htail := ih (hne := by simp) (U := operator_image s.1 U) (composed_domains hcomp).2
        (fun m => by
          simpa only [List.map_cons, List.get_cons_succ', Fin.val_succ, prefixDomain_cons_succ]
            using hstep m.succ)
      simpa only [List.map_cons, chain_cons, matrixProduct_cons] using compose hcomp hfirst htail

variable [Nonempty I] (G : GaugeFamily X I bot)

theorem chain_lip
    (steps : List (Operator X bot × BoundMatrix I)) (hne : steps ≠ []) (U : Set X)
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hstep : ∀ m : Fin steps.length, (steps.get m).2 ∈ lipMatricesOn G (steps.get m).1
      (prefixDomain (steps.map Prod.fst) U m.val)) :
    matrixProduct (steps.map Prod.snd) ∈ lipMatricesOn G (chain (steps.map Prod.fst)) U :=
  chain_bounds (IsLipOn G) (fun h => lip_comp G h) steps hne U hU hstep

theorem chain_colip
    (steps : List (Operator X bot × BoundMatrix I)) (hne : steps ≠ []) (U : Set X)
    (hU : U ⊆ dom (chain (steps.map Prod.fst)))
    (hstep : ∀ m : Fin steps.length, (steps.get m).2 ∈ coLipMatricesOn G (steps.get m).1
      (prefixDomain (steps.map Prod.fst) U m.val)) :
    matrixProduct (steps.map Prod.snd) ∈ coLipMatricesOn G (chain (steps.map Prod.fst)) U :=
  chain_bounds (IsCoLipOn G) (fun h => colip_comp G h) steps hne U hU hstep

end LCH02
