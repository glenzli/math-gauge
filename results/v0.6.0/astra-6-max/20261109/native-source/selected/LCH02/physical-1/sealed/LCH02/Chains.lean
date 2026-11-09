import LCH02.Bounds

open scoped BigOperators Classical Matrix
open formal_oet.vol_01.ch_01_foundations

namespace LCH02

variable {X : Type} {bot : X}

/-- [φ₁,...,φₖ] is executed left to right, yielding φₖ ∘ ... ∘ φ₁. -/
def chain : List (Operator X bot) → Operator X bot
  | [] => 1
  | φ :: ps => chain ps * φ

@[simp] theorem chain_nil : chain ([] : List (Operator X bot)) = 1 := rfl

@[simp] theorem chain_cons (φ : Operator X bot) (ps : List (Operator X bot)) :
    chain (φ :: ps) = chain ps * φ := rfl

@[simp] theorem chain_singleton (φ : Operator X bot) : chain [φ] = φ := by
  simp [chain]

theorem chain_eq_frozen (ps : List (Operator X bot)) :
    chain ps = OperatorChain ps.reverse := by
  rw [operator_chain_eq_prod]
  induction ps with
  | nil => rfl
  | cons φ ps ih => simp [chain, ih, List.reverse_cons, List.prod_append]

theorem chain_append (ps qs : List (Operator X bot)) :
    chain (ps ++ qs) = chain qs * chain ps := by
  induction ps with
  | nil => simp
  | cons φ ps ih => simp [ih, mul_assoc]

/-- The textbook Uₘ is intermediate ps U₁ (m-1). -/
def intermediate (ps : List (Operator X bot)) (U : Set X) (n : ℕ) : Set X :=
  (chain (ps.take n)).func '' U

@[simp] theorem intermediate_zero (ps : List (Operator X bot)) (U : Set X) :
    intermediate ps U 0 = U := by
  change (id : X → X) '' U = U
  exact Set.image_id U

@[simp] theorem intermediate_cons_succ (φ : Operator X bot)
    (ps : List (Operator X bot)) (U : Set X) (n : ℕ) :
    intermediate (φ :: ps) U (n + 1) = intermediate ps (φ.func '' U) n := by
  simp only [intermediate, List.take_succ_cons, chain_cons, Set.image_image]
  rfl

theorem intermediate_step (ps : List (Operator X bot)) (U : Set X)
    (n : ℕ) (hn : n < ps.length) :
    intermediate ps U (n + 1) = ps[n].func '' intermediate ps U n := by
  simp only [intermediate, List.take_succ_eq_append_getElem hn,
    chain_append, chain_singleton, Set.image_image]
  rfl

@[simp] theorem intermediate_final (ps : List (Operator X bot)) (U : Set X) :
    intermediate ps U ps.length = (chain ps).func '' U := by
  simp [intermediate]

/-- Full-composite legality forces legality at every actual input domain. -/
theorem intermediate_legal (ps : List (Operator X bot)) {U : Set X}
    (hU : U ⊆ dom (chain ps)) :
    ∀ n (hn : n < ps.length), intermediate ps U n ⊆ dom ps[n] := by
  induction ps generalizing U with
  | nil => intro n hn; simp at hn
  | cons φ ps ih =>
      intro n hn
      have hdom := composite_domain φ (chain ps) hU
      cases n with
      | zero => simpa using hdom.1
      | succ n =>
          simpa using ih hdom.2 n (by simpa using hn)

/-- A step stores only an operator and its chosen matrix, never a chain bound. -/
abbrev Step (X : Type) (bot : X) (I : Type) := Operator X bot × Mat I

section Gauge
variable {I : Type} [Fintype I] [Nonempty I] {d : I → X → X → ENNReal}
variable (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
include hd

theorem chain_lip (ss : List (Step X bot I)) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hsteps : ∀ n (hn : n < ss.length),
      IsLipOn d ss[n].1 (intermediate (ss.map Prod.fst) U n) ss[n].2) :
    IsLipOn d (chain (ss.map Prod.fst)) U (matrixProduct (ss.map Prod.snd)) := by
  induction ss generalizing U with
  | nil => simpa using identity_lip hd hU
  | cons s ss ih =>
      have h₀ : IsLipOn d s.1 U s.2 := by
        simpa using hsteps 0 (by simp)
      have ht : ∀ n (hn : n < ss.length),
          IsLipOn d ss[n].1
            (intermediate (ss.map Prod.fst) (s.1.func '' U) n) ss[n].2 := by
        intro n hn
        simpa using hsteps (n + 1) (by simpa using hn)
      have hdom := (composite_domain s.1 (chain (ss.map Prod.fst)) hU).2
      exact lip_comp hd hU h₀ (ih hdom ht)

theorem finite_lip (ss : List (Step X bot I)) (_hne : ss ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hsteps : ∀ n (hn : n < ss.length),
      IsLipOn d ss[n].1 (intermediate (ss.map Prod.fst) U n) ss[n].2) :
    IsLipOn d (chain (ss.map Prod.fst)) U (matrixProduct (ss.map Prod.snd)) :=
  chain_lip hd ss hU hsteps

theorem chain_colip (ss : List (Step X bot I)) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hsteps : ∀ n (hn : n < ss.length),
      IsCoLipOn d ss[n].1 (intermediate (ss.map Prod.fst) U n) ss[n].2) :
    IsCoLipOn d (chain (ss.map Prod.fst)) U (matrixProduct (ss.map Prod.snd)) := by
  induction ss generalizing U with
  | nil => simpa using identity_colip hd hne hU
  | cons s ss ih =>
      have h₀ : IsCoLipOn d s.1 U s.2 := by
        simpa using hsteps 0 (by simp)
      have ht : ∀ n (hn : n < ss.length),
          IsCoLipOn d ss[n].1
            (intermediate (ss.map Prod.fst) (s.1.func '' U) n) ss[n].2 := by
        intro n hn
        simpa using hsteps (n + 1) (by simpa using hn)
      have hdom := (composite_domain s.1 (chain (ss.map Prod.fst)) hU).2
      exact colip_comp hd hU h₀ (ih (hne.image s.1.func) hdom ht)

/-- Nonemptiness of U is obtained from the first local co-Lip certificate. -/
theorem finite_colip (ss : List (Step X bot I)) (hne : ss ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hsteps : ∀ n (hn : n < ss.length),
      IsCoLipOn d ss[n].1 (intermediate (ss.map Prod.fst) U n) ss[n].2) :
    IsCoLipOn d (chain (ss.map Prod.fst)) U (matrixProduct (ss.map Prod.snd)) := by
  apply chain_colip hd ss _ hU hsteps
  cases ss with
  | nil => exact (hne rfl).elim
  | cons s ss => simpa using (hsteps 0 (by simp)).1

end Gauge
end LCH02
