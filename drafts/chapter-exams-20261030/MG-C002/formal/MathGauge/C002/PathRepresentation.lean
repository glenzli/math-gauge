import MathGauge.C002.Completeness

namespace MathGauge.C002

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

noncomputable section

variable {I X : Type} {bot : X} [Fintype I]

theorem chain_domain_excludes_bot (φs : List (Operator X bot)) (U : Set X)
    (hdom : U ⊆ dom (OperatorChain φs)) : ∀ x ∈ U, x ≠ bot := by
  intro x hx hb
  exact hdom hx (by rw [hb,(OperatorChain φs).preserves_bot])

theorem chain_domain_at_outer_step (φ : Operator X bot) (tail : List (Operator X bot))
    (U : Set X) (hdom : U ⊆ dom (OperatorChain (φ::tail))) :
    U ⊆ dom (OperatorChain tail) ∧ (OperatorChain tail).func '' U ⊆ dom φ := by
  constructor
  · intro x hx hb
    have h := hdom hx
    change φ.func ((OperatorChain tail).func x) ≠ bot at h
    exact h (by rw [hb,φ.preserves_bot])
  · rintro y ⟨x,hx,rfl⟩
    exact hdom hx

def stepwise_lip (d : I → X → X → ENNReal) (U : Set X) :
    List (Operator X bot × (I → I → ENNReal)) → Prop
  | [] => True
  | (φ,L) :: steps => stepwise_lip d U steps ∧
      IsLipMatrix d φ ((OperatorChain (steps.map Prod.fst)).func '' U) L

def stepwise_colip (d : I → X → X → ENNReal) (U : Set X) :
    List (Operator X bot × (I → I → ENNReal)) → Prop
  | [] => True
  | (φ,K) :: steps => stepwise_colip d U steps ∧
      IsCoLipMatrix d φ ((OperatorChain (steps.map Prod.fst)).func '' U) K

theorem construct_lip_chain (d : I → X → X → ENNReal) (U : Set X)
    (hU : ∀ x ∈ U, x ≠ bot) (steps : List (Operator X bot × (I → I → ENNReal)))
    (h : stepwise_lip d U steps) :
    RightChainLipCertificateList d (steps.map Prod.fst) U (steps.map Prod.snd) := by
  induction steps with
  | nil => exact .nil U hU
  | cons p steps ih => exact .cons p.1 _ U p.2 _ (ih h.1) h.2

theorem construct_colip_chain (d : I → X → X → ENNReal) (U : Set X)
    (hU : ∀ x ∈ U, x ≠ bot) (hne : U.Nonempty)
    (steps : List (Operator X bot × (I → I → ENNReal))) (h : stepwise_colip d U steps) :
    RightChainCoLipCertificateList d (steps.map Prod.fst) U (steps.map Prod.snd) := by
  induction steps with
  | nil => exact .nil U hU hne
  | cons p steps ih => exact .cons p.1 _ U p.2 _ (ih h.1) h.2

/-- The exact product follows from the local inequalities at all actual intermediate images. -/
theorem arbitrary_finite_lip_composition (d : I → X → X → ENNReal) (U : Set X)
    (hU : ∀ x ∈ U, x ≠ bot) (steps : List (Operator X bot × (I → I → ENNReal)))
    (h : stepwise_lip d U steps) :
    IsLipMatrix d (OperatorChain (steps.map Prod.fst)) U (matrix_list_mul (steps.map Prod.snd)) :=
  list_lip_certificates_product (construct_lip_chain d U hU steps h)

theorem arbitrary_finite_colip_composition (d : I → X → X → ENNReal) (U : Set X)
    (hU : ∀ x ∈ U, x ≠ bot) (hne : U.Nonempty)
    (steps : List (Operator X bot × (I → I → ENNReal))) (h : stepwise_colip d U steps) :
    IsCoLipMatrix d (OperatorChain (steps.map Prod.fst)) U (matrix_list_mul (steps.map Prod.snd)) :=
  list_colip_certificates_product (construct_colip_chain d U hU hne steps h)

theorem MatrixPath.vertices_head {Ms : List (I → I → ENNReal)} {i j : I}
    (p : MatrixPath Ms i j) : p.vertices.head? = some j := by
  cases p <;> rfl

theorem MatrixPath.vertices_last {Ms : List (I → I → ENNReal)} {i j : I}
    (p : MatrixPath Ms i j) : p.vertices.getLast? = some i := by
  induction p with
  | nil => rfl
  | cons M j tail ih =>
      cases tail <;> simpa [MatrixPath.vertices] using ih

/-- Every list of n+1 indices with the prescribed endpoints reconstructs a path. -/
theorem index_sequence_to_path (Ms : List (I → I → ENNReal)) (v : List I) (i j : I)
    (hlen : v.length = Ms.length + 1) (hfirst : v.head? = some j)
    (hlast : v.getLast? = some i) : ∃ p : MatrixPath Ms i j, p.vertices = v := by
  induction Ms generalizing v i j with
  | nil =>
      cases v with
      | nil => simp at hlen
      | cons a tail =>
          have ht : tail = [] := by simpa using hlen
          subst tail
          simp only [List.head?_cons, Option.some.injEq] at hfirst
          simp only [List.getLast?_singleton, Option.some.injEq] at hlast
          subst a; subst i
          exact ⟨.nil j,rfl⟩
  | cons M Ms ih =>
      cases v with
      | nil => simp at hlen
      | cons a tail =>
          simp only [List.head?_cons, Option.some.injEq] at hfirst
          subst a
          cases tail with
          | nil => simp at hlen
          | cons k rest =>
              have htlen : (k::rest).length = Ms.length + 1 := by simpa using hlen
              have htlast : (k::rest).getLast? = some i := by simpa using hlast
              obtain ⟨p,hp⟩ := ih (k::rest) i k htlen rfl htlast
              refine ⟨.cons M j p,?_⟩
              simp [MatrixPath.vertices,hp]

theorem MatrixPath.vertices_injective {Ms : List (I → I → ENNReal)} {i j : I}
    (p q : MatrixPath Ms i j) (h : p.vertices = q.vertices) : p = q := by
  induction p with
  | nil => cases q; rfl
  | cons M j tail ih =>
      cases q with
      | cons _ _ tail' =>
          have ht : tail.vertices = tail'.vertices := List.cons.inj h |>.2
          have he := congrArg List.head? ht
          rw [tail.vertices_head,tail'.vertices_head] at he
          cases Option.some.inj he
          exact congrArg (MatrixPath.cons M j) (ih tail' ht)

def MatrixPath.weight : {Ms : List (I → I → ENNReal)} → {i j : I} →
    MatrixPath Ms i j → ENNReal
  | _,_,_,.nil _ => 1
  | _,_,_,.cons (k := k) M j tail => M k j * tail.weight

/-- Index lists run from output j back to input i, matching the matrix list order. -/
def sequence_weight : List (I → I → ENNReal) → List I → ENNReal
  | [], [_] => 1
  | M::Ms, j::k::rest => M k j * sequence_weight Ms (k::rest)
  | _,_ => 0

theorem MatrixPath.weight_matches_sequence {Ms : List (I → I → ENNReal)} {i j : I}
    (p : MatrixPath Ms i j) : p.weight = sequence_weight Ms p.vertices := by
  induction p with
  | nil => rfl
  | cons M j tail ih =>
      cases tail <;> simpa [MatrixPath.weight,MatrixPath.vertices,sequence_weight] using
        congrArg (fun z => M _ j * z) ih

theorem MatrixPath.weight_positive_iff {Ms : List (I → I → ENNReal)} {i j : I}
    (p : MatrixPath Ms i j) : 0 < p.weight ↔ p.all_positive := by
  induction p with
  | nil => simp [MatrixPath.weight,MatrixPath.all_positive]
  | cons M j tail ih =>
      simp only [MatrixPath.weight,MatrixPath.all_positive,ENNReal.mul_pos_iff,ih]

end
end MathGauge.C002
