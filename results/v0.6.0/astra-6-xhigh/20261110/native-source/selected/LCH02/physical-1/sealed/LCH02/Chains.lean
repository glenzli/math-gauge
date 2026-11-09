import LCH02.Products

noncomputable section

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

variable {X : Type} {bot : X}

/-- Only the first n operators are used; φ 0 is the book's φ₁. -/
def chain (φ : ℕ → Operator X bot) (n : ℕ) : Operator X bot := orderedProduct φ n

@[simp] theorem chain_zero (φ : ℕ → Operator X bot) : chain φ 0 = 1 := rfl

@[simp] theorem chain_succ (φ : ℕ → Operator X bot) (n : ℕ) :
    chain φ (n + 1) = φ n * chain φ n := rfl

theorem chain_eq_frozen (φ : ℕ → Operator X bot) (n : ℕ) :
    chain φ n = OperatorChain ((List.range n).reverse.map φ) := by
  rw [operator_chain_eq_prod]
  exact orderedProduct_eq_reverse_prod φ n

/-- This is U_{m+1} in the book, including m = 0. -/
def inputDomain (φ : ℕ → Operator X bot) (U : Set X) (m : ℕ) : Set X :=
  (chain φ m).func '' U

@[simp] theorem inputDomain_zero (φ : ℕ → Operator X bot) (U : Set X) :
    inputDomain φ U 0 = U := by
  change id '' U = U
  exact Set.image_id U

theorem inputDomain_succ (φ : ℕ → Operator X bot) (U : Set X) (m : ℕ) :
    inputDomain φ U (m + 1) = (φ m).func '' inputDomain φ U m := by
  change ((φ m).func ∘ (chain φ m).func) '' U =
    (φ m).func '' ((chain φ m).func '' U)
  rw [Set.image_image]
  rfl

theorem chain_dom_mono (φ : ℕ → Operator X bot) {m n : ℕ} (hmn : m ≤ n) :
    dom (chain φ n) ⊆ dom (chain φ m) := by
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := Nat.eq_zero_of_le_zero hmn
      subst m
      exact fun _ hx => hx
  | succ n ih =>
      by_cases hm : m ≤ n
      · have hstep : dom (chain φ (n + 1)) ⊆ dom (chain φ n) :=
          (composition_domains (φ₁ := chain φ n) (φ₂ := φ n)
            (fun _ hx => hx)).1
        exact hstep.trans (ih hm)
      · have hm' : m = n + 1 := by omega
        subst m
        exact fun _ hx => hx

theorem inputDomain_subset_dom (φ : ℕ → Operator X bot) {U : Set X} {n m : ℕ}
    (hU : U ⊆ dom (chain φ n)) (hm : m < n) :
    inputDomain φ U m ⊆ dom (φ m) := by
  rintro z ⟨x, hx, rfl⟩
  change (chain φ (m + 1)).func x ≠ bot
  exact chain_dom_mono φ (Nat.succ_le_of_lt hm) (hU hx)

theorem inputDomain_nonempty (φ : ℕ → Operator X bot) {U : Set X}
    (hne : U.Nonempty) (m : ℕ) : (inputDomain φ U m).Nonempty :=
  hne.image _

variable {I : Type} [Fintype I] [DecidableEq I]
    {d : I → X → X → ENNReal}

theorem chain_lip (φ : ℕ → Operator X bot) (L : ℕ → Mat I) (U : Set X) (n : ℕ) :
    U ⊆ dom (chain φ n) →
    (∀ m < n, LipOn d (φ m) (inputDomain φ U m) (L m)) →
    LipOn d (chain φ n) U (matrixProduct L n) := by
  induction n with
  | zero =>
      intro hU _
      exact identity_lip hU
  | succ n ih =>
      intro hU hs
      have hp := ih (hU.trans (chain_dom_mono φ (Nat.le_succ n)))
        (fun m hm => hs m (Nat.lt_succ_of_lt hm))
      exact lip_comp hU hp (hs n (Nat.lt_succ_self n))

theorem finite_lip (φ : ℕ → Operator X bot) (L : ℕ → Mat I)
    (U : Set X) (n : ℕ) (_hn : 0 < n) (hU : U ⊆ dom (chain φ n))
    (hs : ∀ m < n, LipOn d (φ m) (inputDomain φ U m) (L m)) :
    LipOn d (chain φ n) U (matrixProduct L n) :=
  chain_lip φ L U n hU hs

theorem chain_coLip (φ : ℕ → Operator X bot) (K : ℕ → Mat I) (U : Set X)
    (hne : U.Nonempty) (n : ℕ) :
    U ⊆ dom (chain φ n) →
    (∀ m < n, CoLipOn d (φ m) (inputDomain φ U m) (K m)) →
    CoLipOn d (chain φ n) U (matrixProduct K n) := by
  induction n with
  | zero =>
      intro hU _
      exact identity_coLip hne hU
  | succ n ih =>
      intro hU hs
      have hp := ih (hU.trans (chain_dom_mono φ (Nat.le_succ n)))
        (fun m hm => hs m (Nat.lt_succ_of_lt hm))
      exact coLip_comp hU hp (hs n (Nat.lt_succ_self n))

theorem finite_coLip (φ : ℕ → Operator X bot) (K : ℕ → Mat I)
    (U : Set X) (n : ℕ) (hn : 0 < n) (hU : U ⊆ dom (chain φ n))
    (hs : ∀ m < n, CoLipOn d (φ m) (inputDomain φ U m) (K m)) :
    CoLipOn d (chain φ n) U (matrixProduct K n) := by
  have hne : U.Nonempty := by simpa using (hs 0 hn).1
  exact chain_coLip φ K U hne n hU hs

end LCH02
