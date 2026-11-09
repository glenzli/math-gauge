import LCH02.Bounds

namespace LCH02

noncomputable section

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X}

/-- Operators are listed in execution order, so the head acts first. -/
def chain : List (Operator X bot) → Operator X bot
  | [] => 1
  | φ :: fs => chain fs * φ

theorem chain_eq_frozen (fs : List (Operator X bot)) :
    chain fs = OperatorChain fs.reverse := by
  rw [operator_chain_eq_prod]
  induction fs with
  | nil => rfl
  | cons φ fs ih => simp [chain, List.reverse_cons, ih]

/-- Zero-based step `m` has input domain `U_(m+1)` in the text. -/
def actualDomain (fs : List (Operator X bot)) (U : Set X) (m : ℕ) : Set X :=
  (chain (fs.take m)).func '' U

@[simp] theorem actualDomain_zero (fs : List (Operator X bot)) (U : Set X) :
    actualDomain fs U 0 = U := by
  change id '' U = U
  simp

theorem actualDomain_cons_succ (φ : Operator X bot) (fs : List (Operator X bot))
    (U : Set X) (m : ℕ) :
    actualDomain (φ :: fs) U (m + 1) = actualDomain fs (φ.func '' U) m := by
  unfold actualDomain
  rw [List.take_succ_cons, chain, Set.image_image]
  rfl

theorem actualDomain_last (fs : List (Operator X bot)) (U : Set X) :
    actualDomain fs U fs.length = (chain fs).func '' U := by
  simp [actualDomain]

theorem actualDomain_subset_dom (fs : List (Operator X bot)) (U : Set X)
    (hU : U ⊆ dom (chain fs)) :
    ∀ m (hm : m < fs.length), actualDomain fs U m ⊆ dom (fs[m]) := by
  induction fs generalizing U with
  | nil => intro m hm; simp at hm
  | cons φ fs ih =>
      intro m hm
      cases m with
      | zero =>
          simpa using subset_dom_first_of_comp φ (chain fs) hU
      | succ m =>
          have ht := image_subset_dom_of_comp φ (chain fs) hU
          simpa only [actualDomain_cons_succ, List.getElem_cons_succ] using
            ih (φ.func '' U) ht m (by simpa using hm)

variable [Fintype I] [DecidableEq I] (d : I → X → X → ENNReal)

/-- A list of pairs contains only operators and matrices, without proof fields.
Every hypothesis is a single-step inequality on its exact actual input image. -/
theorem chain_lip (ss : List (Operator X bot × BoundMatrix I)) (U : Set X)
    (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hstep : ∀ m (hm : m < ss.length),
      IsRestrictedLip d (ss[m]).1 (actualDomain (ss.map Prod.fst) U m) (ss[m]).2) :
    IsRestrictedLip d (chain (ss.map Prod.fst)) U (orderedProduct (ss.map Prod.snd)) := by
  induction ss generalizing U with
  | nil => exact identity_lip d U hU
  | cons s ss ih =>
      have hhead : IsRestrictedLip d s.1 U s.2 := by
        simpa using hstep 0 (by simp)
      have htail : IsRestrictedLip d (chain (ss.map Prod.fst)) (s.1.func '' U)
          (orderedProduct (ss.map Prod.snd)) := by
        apply ih (s.1.func '' U) (image_subset_dom_of_comp s.1 (chain (ss.map Prod.fst)) hU)
        intro m hm
        simpa only [List.getElem_cons_succ, List.map_cons, actualDomain_cons_succ] using
          hstep (m + 1) (by simpa using hm)
      exact lip_comp d s.1 (chain (ss.map Prod.fst)) U s.2
        (orderedProduct (ss.map Prod.snd)) hU hhead htail

theorem chain_coLip_of_nonempty (ss : List (Operator X bot × BoundMatrix I))
    (U : Set X) (hne : U.Nonempty) (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hstep : ∀ m (hm : m < ss.length),
      IsRestrictedCoLip d (ss[m]).1 (actualDomain (ss.map Prod.fst) U m) (ss[m]).2) :
    IsRestrictedCoLip d (chain (ss.map Prod.fst)) U (orderedProduct (ss.map Prod.snd)) := by
  induction ss generalizing U with
  | nil => exact identity_coLip d U hne hU
  | cons s ss ih =>
      have hhead : IsRestrictedCoLip d s.1 U s.2 := by
        simpa using hstep 0 (by simp)
      have htail : IsRestrictedCoLip d (chain (ss.map Prod.fst)) (s.1.func '' U)
          (orderedProduct (ss.map Prod.snd)) := by
        apply ih (s.1.func '' U) (hne.image s.1.func)
          (image_subset_dom_of_comp s.1 (chain (ss.map Prod.fst)) hU)
        intro m hm
        simpa only [List.getElem_cons_succ, List.map_cons, actualDomain_cons_succ] using
          hstep (m + 1) (by simpa using hm)
      exact coLip_comp d s.1 (chain (ss.map Prod.fst)) U s.2
        (orderedProduct (ss.map Prod.snd)) hU hhead htail

/-- For a positive length chain, nonemptiness follows from the first co-Lip premise. -/
theorem chain_coLip (ss : List (Operator X bot × BoundMatrix I))
    (hlen : 0 < ss.length) (U : Set X) (hU : U ⊆ dom (chain (ss.map Prod.fst)))
    (hstep : ∀ m (hm : m < ss.length),
      IsRestrictedCoLip d (ss[m]).1 (actualDomain (ss.map Prod.fst) U m) (ss[m]).2) :
    IsRestrictedCoLip d (chain (ss.map Prod.fst)) U (orderedProduct (ss.map Prod.snd)) := by
  have hne : U.Nonempty := by simpa using (hstep 0 hlen).1
  exact chain_coLip_of_nonempty d ss U hne hU hstep

end
end LCH02
