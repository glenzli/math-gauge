import LCH02.Bounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations
open scoped Classical
noncomputable section

abbrev Step (X I : Type) (b : X) := Operator X b × Mat I

variable {X I : Type} {b : X}

def chain (s : List (Step X I b)) : Operator X b := OperatorChain (s.map Prod.fst)

def chainMatrix [Fintype I] (s : List (Step X I b)) : Mat I := orderedProduct (s.map Prod.snd)

def reached (s : List (Step X I b)) (U : Set X) : Set X := (chain s).func '' U

theorem chain_nil : chain ([] : List (Step X I b)) = 1 := rfl

theorem chain_cons (a : Step X I b) (s : List (Step X I b)) :
    chain (a :: s) = a.1 * chain s := rfl

theorem reached_nil (U : Set X) : reached ([] : List (Step X I b)) U = U := Set.image_id U

theorem reached_cons (a : Step X I b) (s : List (Step X I b)) (U : Set X) :
    reached (a :: s) U = a.1.func '' reached s U :=
  (Set.image_image a.1.func (chain s).func U).symm

/-- Each suffix is the part of the chain already executed. -/
def Along (P : Operator X b → Set X → Mat I → Prop) (U : Set X) : List (Step X I b) → Prop
  | [] => True
  | a :: s => Along P U s ∧ P a.1 (reached s U) a.2

theorem along_iff (P : Operator X b → Set X → Mat I → Prop) (U : Set X) (s : List (Step X I b)) :
    Along P U s ↔ ∀ n (hn : n < s.length), P s[n].1 (reached (s.drop (n + 1)) U) s[n].2 := by
  induction s with
  | nil => simp [Along]
  | cons a s ih =>
    constructor
    · intro h n hn
      cases n with
      | zero => exact h.2
      | succ n => exact ih.mp h.1 n (Nat.lt_of_succ_lt_succ hn)
    · intro h
      exact ⟨ih.mpr (fun n hn => h (n + 1) (Nat.succ_lt_succ hn)), h 0 (Nat.zero_lt_succ _)⟩

private theorem split_domain {f g : Operator X b} {U : Set X} (h : U ⊆ dom (g * f)) :
    U ⊆ dom f ∧ f.func '' U ⊆ dom g := by
  constructor
  · intro x hx heq
    apply h hx
    change g.func (f.func x) = b
    rw [heq, g.preserves_bot]
  · rintro _ ⟨x, hx, rfl⟩
    exact h hx

theorem step_domains (s : List (Step X I b)) {U : Set X} (hd : U ⊆ dom (chain s)) :
    Along (fun f V _ => V ⊆ dom f) U s := by
  induction s with
  | nil => trivial
  | cons a s ih =>
    obtain ⟨hpre, him⟩ := split_domain (f := chain s) (g := a.1) hd
    exact ⟨ih hpre, him⟩

variable [Fintype I] [Nonempty I] (G : Gauge X I b) {U : Set X}

theorem finite_lip (a : Step X I b) (s : List (Step X I b)) (hd : U ⊆ dom (chain (a :: s)))
    (hs : Along (LipOn G) U (a :: s)) : chainMatrix (a :: s) ∈ lipFamilyOn G (chain (a :: s)) U := by
  induction s generalizing a with
  | nil => simpa [chainMatrix, orderedProduct, chain_cons, chain_nil, reached_nil] using hs.2
  | cons t s ih =>
    have hpre := (split_domain (f := chain (t :: s)) (g := a.1) hd).1
    exact lip_comp G hd (ih t hpre hs.1) hs.2

theorem finite_coLip (a : Step X I b) (s : List (Step X I b)) (hd : U ⊆ dom (chain (a :: s)))
    (hs : Along (CoLipOn G) U (a :: s)) : chainMatrix (a :: s) ∈ coLipFamilyOn G (chain (a :: s)) U := by
  induction s generalizing a with
  | nil => simpa [chainMatrix, orderedProduct, chain_cons, chain_nil, reached_nil] using hs.2
  | cons t s ih =>
    have hpre := (split_domain (f := chain (t :: s)) (g := a.1) hd).1
    exact coLip_comp G hd (ih t hpre hs.1) hs.2

end
end LCH02
