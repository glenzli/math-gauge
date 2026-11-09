import Bounds

namespace HCH02
noncomputable section
open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

def chain : List (Operator X bot) → Operator X bot
  | [] => ident
  | φ :: fs => comp (chain fs) φ

def iterImage : List (Operator X bot) → Set X → Set X
  | [], U => U
  | φ :: fs, U => iterImage fs (φ.func '' U)

def actual : List (Operator X bot) → Set X → ℕ → Set X
  | [], U, _ => U
  | _ :: _, U, 0 => U
  | φ :: fs, U, n + 1 => actual fs (φ.func '' U) n

theorem chain_image (fs : List (Operator X bot)) (U : Set X) :
    (chain fs).func '' U = iterImage fs U := by
  induction fs generalizing U with
  | nil => simp [chain, ident, iterImage]
  | cons φ fs ih =>
    simpa only [chain, comp, Set.image_image] using ih (φ.func '' U)

theorem actual_prefix (fs : List (Operator X bot)) (U : Set X) (n : ℕ) :
    actual fs U n = (chain (fs.take n)).func '' U := by
  induction fs generalizing U n with
  | nil => simp [actual, chain, ident]
  | cons φ fs ih =>
    cases n with
    | zero => simp [actual, chain, ident]
    | succ n => simpa [actual, chain, comp, Set.image_image] using ih (φ.func '' U) n

theorem initial_subset {φ ψ : Operator X bot} {U : Set X}
    (hU : U ⊆ dom (comp ψ φ)) : U ⊆ dom φ :=
  fun x hx => ((comp_dom ψ φ x).mp (hU hx)).1

theorem image_subset {φ ψ : Operator X bot} {U : Set X}
    (hU : U ⊆ dom (comp ψ φ)) : φ.func '' U ⊆ dom ψ := by
  rintro y ⟨x, hx, rfl⟩
  exact ((comp_dom ψ φ x).mp (hU hx)).2

theorem actual_domain (fs : List (Operator X bot)) {U : Set X}
    (hU : U ⊆ dom (chain fs)) (n : ℕ) (hn : n < fs.length) :
    actual fs U n ⊆ dom fs[n] := by
  induction fs generalizing U n with
  | nil => simp at hn
  | cons φ fs ih =>
    cases n with
    | zero => exact initial_subset hU
    | succ n => exact ih (image_subset hU) n (Nat.lt_of_succ_lt_succ hn)

theorem chain_append (fs gs : List (Operator X bot)) :
    chain (fs ++ gs) = comp (chain gs) (chain fs) := by
  induction fs with
  | nil => ext x; rfl
  | cons φ fs ih =>
    simp only [List.cons_append, chain, ih]
    rfl

theorem chain_frozen (fs : List (Operator X bot)) : chain fs = OperatorChain fs.reverse := by
  induction fs using List.reverseRecOn with
  | nil => rfl
  | append_singleton fs φ ih =>
    rw [chain_append, List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append, OperatorChain, ← ih]
    ext x
    rfl

theorem display_eye : display (eye : Mat I) = (1 : Matrix I I ENNReal) := by
  ext j i
  simp [display, eye, Matrix.one_apply, eq_comm]

theorem display_product (As : List (Mat I)) :
    display (mprod As) = ((As.map display).reverse).prod := by
  induction As with
  | nil => exact display_eye
  | cons A As ih =>
    simp only [mprod_cons, display_mul, ih, List.map_cons, List.reverse_cons,
      List.prod_append, List.prod_singleton]

def OnSteps (P : Operator X bot → Set X → Mat I → Prop) :
    Set X → List (Operator X bot × Mat I) → Prop
  | _, [] => True
  | U, s :: ss => P s.1 U s.2 ∧ OnSteps P (s.1.func '' U) ss

theorem onSteps_iff (P : Operator X bot → Set X → Mat I → Prop)
    (ss : List (Operator X bot × Mat I)) (U : Set X) :
    OnSteps P U ss ↔ ∀ n (hn : n < ss.length),
      P ss[n].1 (actual (ss.map Prod.fst) U n) ss[n].2 := by
  induction ss generalizing U with
  | nil => simp [OnSteps]
  | cons s ss ih =>
    constructor
    · rintro ⟨h, hs⟩ n hn
      cases n with
      | zero => exact h
      | succ n => exact (ih _).mp hs n (Nat.lt_of_succ_lt_succ hn)
    · intro h
      refine ⟨h 0 (by simp), (ih _).mpr ?_⟩
      intro n hn
      exact h (n + 1) (Nat.succ_lt_succ hn)

theorem lip_chain {d : I → X → X → ENNReal}
    (ss : List (Operator X bot × Mat I)) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hs : OnSteps (fun φ V M => M ∈ Lip d φ V) U ss) :
    mprod (ss.map Prod.snd) ∈ Lip d (chain (ss.map Prod.fst)) U := by
  induction ss generalizing U with
  | nil => exact identity_lip hU
  | cons s ss ih =>
    exact lip_comp hU hs.1 (ih (image_subset hU) hs.2)

theorem colip_chain {d : I → X → X → ENNReal}
    (ss : List (Operator X bot × Mat I)) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst))) (hne : U.Nonempty)
    (hs : OnSteps (fun φ V M => M ∈ CoLip d φ V) U ss) :
    mprod (ss.map Prod.snd) ∈ CoLip d (chain (ss.map Prod.fst)) U := by
  induction ss generalizing U with
  | nil => exact identity_colip hU hne
  | cons s ss ih =>
    exact colip_comp hU hs.1 (ih (image_subset hU) (hne.image _) hs.2)

theorem colip_chain_positive {d : I → X → X → ENNReal}
    (ss : List (Operator X bot × Mat I)) (hlen : ss ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hs : OnSteps (fun φ V M => M ∈ CoLip d φ V) U ss) :
    mprod (ss.map Prod.snd) ∈ CoLip d (chain (ss.map Prod.fst)) U := by
  cases ss with
  | nil => exact (hlen rfl).elim
  | cons s ss => exact colip_chain _ hU hs.1.1 hs

theorem lip_chain_indexed {d : I → X → X → ENNReal}
    (ss : List (Operator X bot × Mat I)) (_hlen : ss ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hs : ∀ n (hn : n < ss.length),
      ss[n].2 ∈ Lip d ss[n].1 (actual (ss.map Prod.fst) U n)) :
    mprod (ss.map Prod.snd) ∈ Lip d (chain (ss.map Prod.fst)) U :=
  lip_chain ss hU ((onSteps_iff _ ss U).mpr hs)

theorem colip_chain_indexed {d : I → X → X → ENNReal}
    (ss : List (Operator X bot × Mat I)) (hlen : ss ≠ []) {U : Set X}
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hs : ∀ n (hn : n < ss.length),
      ss[n].2 ∈ CoLip d ss[n].1 (actual (ss.map Prod.fst) U n)) :
    mprod (ss.map Prod.snd) ∈ CoLip d (chain (ss.map Prod.fst)) U :=
  colip_chain_positive ss hlen hU ((onSteps_iff _ ss U).mpr hs)

end
end HCH02
