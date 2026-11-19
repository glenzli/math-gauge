import LCH02.Bounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped Classical

variable {X : Type} {b : X}

/-- Time index zero is the first operator to act. -/
abbrev chain {n : ℕ} (f : Fin n → Operator X b) : Operator X b := orderedProd f

@[simp] theorem chain_empty (f : Fin 0 → Operator X b) : chain f = operator_identity := rfl

theorem chain_eq_operatorChain {n : ℕ} (f : Fin n → Operator X b) :
    chain f = OperatorChain (List.ofFn f).reverse := by
  rw [operator_chain_eq_prod]
  exact orderedProd_eq_reverse_prod f

/-- Stage zero is the initial set. Each recursive call starts on the exact image. -/
def stage : {n : ℕ} → (Fin n → Operator X b) → Set X → Fin (n + 1) → Set X
  | 0, _, U, _ => U
  | _ + 1, f, U, m => Fin.cases U (stage (Fin.tail f) ((f 0).func '' U)) m

@[simp] theorem stage_zero {n : ℕ} (f : Fin n → Operator X b) (U : Set X) :
    stage f U 0 = U := by cases n <;> rfl

theorem stage_succ {n : ℕ} (f : Fin n → Operator X b) (U : Set X) (m : Fin n) :
    stage f U m.succ = (f m).func '' stage f U m.castSucc := by
  induction n generalizing U with
  | zero => exact m.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) m
    · exact stage_zero (Fin.tail f) _
    · exact ih (Fin.tail f) _ k

theorem stage_last {n : ℕ} (f : Fin n → Operator X b) (U : Set X) :
    stage f U (Fin.last n) = (chain f).func '' U := by
  induction n generalizing U with
  | zero => exact (Set.image_id U).symm
  | succ n ih =>
    change stage (Fin.tail f) ((f 0).func '' U) (Fin.last n) = _
    rw [ih, Set.image_image]
    rfl

theorem stage_nonempty {n : ℕ} (f : Fin n → Operator X b) {U : Set X}
    (hU : U.Nonempty) (m : Fin (n + 1)) : (stage f U m).Nonempty := by
  induction n generalizing U with
  | zero => exact hU
  | succ n ih =>
    refine Fin.cases hU (fun k => ?_) m
    exact ih (Fin.tail f) (hU.image _) k

private theorem image_subset_dom {f g : Operator X b} {U : Set X}
    (hU : U ⊆ dom (g * f)) : f.func '' U ⊆ dom g := by
  rintro _ ⟨x, hx, rfl⟩
  exact hU hx

theorem stage_subset_dom {n : ℕ} (f : Fin n → Operator X b) {U : Set X}
    (hU : U ⊆ dom (chain f)) (m : Fin n) : stage f U m.castSucc ⊆ dom (f m) := by
  induction n generalizing U with
  | zero => exact m.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun k => ?_) m
    · intro x hx hbot
      apply hU hx
      change (chain (Fin.tail f)).func ((f 0).func x) = b
      rw [hbot, (chain (Fin.tail f)).preserves_bot]
    · exact ih (Fin.tail f) (image_subset_dom hU) k

variable {I : Type} [Fintype I] [Nonempty I] (G : Gauge X I b)

theorem chain_lip {n : ℕ} (f : Fin (n + 1) → Operator X b)
    (A : Fin (n + 1) → Bound I) {U : Set X} (hU : U ⊆ dom (chain f))
    (h : ∀ m, A m ∈ lipFamily G (f m) (stage f U m.castSucc)) :
    orderedProd A ∈ lipFamily G (chain f) U := by
  induction n generalizing U with
  | zero => simpa only [chain, orderedProd_one, Fin.castSucc_zero, stage_zero] using h 0
  | succ n ih =>
    apply lip_compose G hU (by simpa only [Fin.castSucc_zero, stage_zero] using h 0)
    exact ih (Fin.tail f) (Fin.tail A) (image_subset_dom hU) (fun m => h m.succ)

theorem chain_coLip {n : ℕ} (f : Fin (n + 1) → Operator X b)
    (A : Fin (n + 1) → Bound I) {U : Set X} (hU : U ⊆ dom (chain f))
    (h : ∀ m, A m ∈ coLipFamily G (f m) (stage f U m.castSucc)) :
    orderedProd A ∈ coLipFamily G (chain f) U := by
  induction n generalizing U with
  | zero => simpa only [chain, orderedProd_one, Fin.castSucc_zero, stage_zero] using h 0
  | succ n ih =>
    apply coLip_compose G hU (by simpa only [Fin.castSucc_zero, stage_zero] using h 0)
    exact ih (Fin.tail f) (Fin.tail A) (image_subset_dom hU) (fun m => h m.succ)

end LCH02
