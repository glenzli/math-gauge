import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Matrix.Basic

/-
Formalization of the supplied historical Chapter 2 of The Operator Evolution Theory.
Mathematical source: Zhe Li / Glen Li / glenzli, https://glenzli.com/books/oet/.
License: CC BY 4.0. This Lean adaptation is AI-generated for the frozen HCH02 task.
-/
namespace HCH02

noncomputable section

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators
open scoped Classical

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

abbrev Mat (I : Type) := I → I → ENNReal

def display (M : Mat I) : Matrix I I ENNReal := fun j i => M i j

def mmul (B A : Mat I) : Mat I := fun i j => ∑ k, B k j * A i k

def action (M : Mat I) (v : I → ENNReal) (j : I) : ENNReal :=
  ∑ i, M i j * v i

theorem display_mul (B A : Mat I) : display (mmul B A) = display B * display A := rfl

noncomputable def eye : Mat I := fun i j => if i = j then 1 else 0

@[simp] theorem action_eye (v : I → ENNReal) (j : I) : action eye v j = v j := by
  classical
  simp [action, eye]

@[simp] theorem mmul_eye (A : Mat I) : mmul A eye = A := by
  classical
  funext i j
  simp [mmul, eye]

@[simp] theorem eye_mmul (A : Mat I) : mmul eye A = A := by
  classical
  funext i j
  simp [mmul, eye]

theorem action_mul (B A : Mat I) (v : I → ENNReal) (j : I) :
    action (mmul B A) v j = action B (fun k => action A v k) j := by
  classical
  simp only [action, mmul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

noncomputable def mprod : List (Mat I) → Mat I
  | [] => eye
  | A :: As => mmul (mprod As) A

@[simp] theorem mprod_nil : mprod ([] : List (Mat I)) = eye := rfl
@[simp] theorem mprod_cons (A : Mat I) (As : List (Mat I)) :
    mprod (A :: As) = mmul (mprod As) A := rfl
@[simp] theorem mprod_singleton (A : Mat I) : mprod [A] = A := by simp

def comp (ψ φ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ φ.func, by simp [φ.preserves_bot, ψ.preserves_bot]⟩

def ident : Operator X bot := ⟨id, rfl⟩

theorem comp_dom (ψ φ : Operator X bot) (x : X) :
    x ∈ dom (comp ψ φ) ↔ x ∈ dom φ ∧ φ.func x ∈ dom ψ := by
  change ψ.func (φ.func x) ≠ bot ↔ φ.func x ≠ bot ∧ ψ.func (φ.func x) ≠ bot
  constructor
  · intro h
    exact ⟨fun e => h (by rw [e, ψ.preserves_bot]), h⟩
  · exact And.right

def Lip (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ action M (fun i => d i x y) j}

def GlobalLip (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  Lip d φ (dom φ)

def CoLip (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {M | U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    action M (fun i => d i x y) j ≤ d j (φ.func x) (φ.func y)}

variable {d : I → X → X → ENNReal} {φ ψ : Operator X bot}
  {U V : Set X} {L K : Mat I}

theorem lip_restrict (h : L ∈ Lip d φ V) (hUV : U ⊆ V) : L ∈ Lip d φ U :=
  ⟨hUV.trans h.1, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem global_lip_restrict (hU : U ⊆ dom φ) : GlobalLip d φ ⊆ Lip d φ U :=
  fun _ h => lip_restrict h hU

theorem lip_family_antitone (hUV : U ⊆ V) : Lip d φ V ⊆ Lip d φ U :=
  fun _ h => lip_restrict h hUV

noncomputable def entryInf (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (i j : I) : ENNReal := sInf {a | ∃ M ∈ Lip d φ U, M i j = a}

theorem entryInf_mono (hUV : U ⊆ V) (i j : I) :
    entryInf d φ U i j ≤ entryInf d φ V i j := by
  apply sInf_le_sInf
  rintro a ⟨M, hM, rfl⟩
  exact ⟨M, lip_restrict hM hUV, rfl⟩

theorem singleton_lip [Subsingleton I] (h : L ∈ Lip d φ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i : I) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  haveI : Unique I := ⟨⟨i⟩, fun a => Subsingleton.elim a i⟩
  have hi : (default : I) = i := Subsingleton.elim _ _
  simpa [action, Finset.univ_unique, hi] using h.2 x hx y hy i

theorem singleton_lip_iff [Subsingleton I] (i : I) :
    L ∈ Lip d φ U ↔ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U,
      d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  constructor
  · intro h
    exact ⟨h.1, fun _ hx _ hy => singleton_lip h hx hy i⟩
  · rintro ⟨hU, h⟩
    refine ⟨hU, ?_⟩
    intro x hx y hy j
    have hj : j = i := Subsingleton.elim _ _
    subst j
    haveI : Unique I := ⟨⟨i⟩, fun a => Subsingleton.elim a i⟩
    have hi : (default : I) = i := Subsingleton.elim _ _
    simpa [action, Finset.univ_unique, hi] using h x hx y hy

theorem lip_comp {A B : Mat I} (hU : U ⊆ dom (comp ψ φ))
    (hA : A ∈ Lip d φ U) (hB : B ∈ Lip d ψ (φ.func '' U)) :
    mmul B A ∈ Lip d (comp ψ φ) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  calc
    d j (ψ.func (φ.func x)) (ψ.func (φ.func y))
        ≤ action B (fun k => d k (φ.func x) (φ.func y)) j :=
      hB.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ action B (fun k => action A (fun i => d i x y) k) j :=
      Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2 x hx y hy k) _
    _ = action (mmul B A) (fun i => d i x y) j := (action_mul _ _ _ _).symm

theorem colip_comp {A B : Mat I} (hU : U ⊆ dom (comp ψ φ))
    (hA : A ∈ CoLip d φ U) (hB : B ∈ CoLip d ψ (φ.func '' U)) :
    mmul B A ∈ CoLip d (comp ψ φ) U := by
  refine ⟨hA.1, hU, ?_⟩
  intro x hx y hy j
  calc
    action (mmul B A) (fun i => d i x y) j
        = action B (fun k => action A (fun i => d i x y) k) j := action_mul _ _ _ _
    _ ≤ action B (fun k => d k (φ.func x) (φ.func y)) j :=
      Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2.2 x hx y hy k) _
    _ ≤ d j (ψ.func (φ.func x)) (ψ.func (φ.func y)) :=
      hB.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem colip_term (h : K ∈ CoLip d φ U) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) :=
  (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y))
    (Finset.mem_univ i)).trans (h.2.2 x hx y hy j)

theorem colip_degenerate (h : K ∈ CoLip d φ (dom φ)) {x y : X}
    (hx : x ∈ dom φ) (hy : y ∈ dom φ) (i j : I)
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K i j = 0 := by
  have hz : K i j * d i x y = 0 := le_antisymm (hout ▸ colip_term h hx hy i j) (zero_le _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hin)

theorem perturb_forward (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom φ ∩ dom ψ) (δ : I → ENNReal)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ d j (φ.func x) (φ.func y) + δ j + δ j := by
  calc
    d j (ψ.func x) (ψ.func y)
        ≤ d j (ψ.func x) (φ.func x) + d j (φ.func x) (ψ.func y) :=
      (hd j).triangle _ _ _
    _ ≤ d j (ψ.func x) (φ.func x) +
        (d j (φ.func x) (φ.func y) + d j (φ.func y) (ψ.func y)) :=
      add_le_add le_rfl ((hd j).triangle _ _ _)
    _ ≤ δ j + (d j (φ.func x) (φ.func y) + δ j) := by
      apply add_le_add
      · rw [(hd j).symm]
        exact hδ x hx j
      · exact add_le_add le_rfl (hδ y hy j)
    _ = _ := by rw [add_left_comm, ← add_assoc]

theorem perturb_reverse (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom φ ∩ dom ψ) (δ : I → ENNReal)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ d j (ψ.func x) (ψ.func y) + δ j + δ j := by
  apply perturb_forward hd (fun z hz => ⟨(hU hz).2, (hU hz).1⟩) δ _ hx hy j
  intro z hz k
  rw [(hd k).symm]
  exact hδ z hz k

theorem perturb_lip (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom φ ∩ dom ψ) (δ : I → ENNReal)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hL : L ∈ Lip d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ action L (fun i => d i x y) j + 2 * δ j := by
  calc
    _ ≤ d j (φ.func x) (φ.func y) + δ j + δ j := perturb_forward hd hU δ hδ hx hy j
    _ ≤ action L (fun i => d i x y) j + δ j + δ j :=
      add_le_add (add_le_add (hL.2 x hx y hy j) le_rfl) le_rfl
    _ = _ := by rw [two_mul, add_assoc]

theorem perturb_colip (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom φ ∩ dom ψ) (δ : I → ENNReal)
    (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hK : K ∈ CoLip d φ U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    action K (fun i => d i x y) j ≤ d j (ψ.func x) (ψ.func y) + 2 * δ j := by
  simpa [two_mul, add_assoc] using
    (hK.2.2 x hx y hy j).trans (perturb_reverse hd hU δ hδ hx hy j)

theorem identity_lip (hU : U ⊆ dom (ident : Operator X bot)) :
    eye ∈ Lip d (ident : Operator X bot) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simp [ident]

theorem identity_colip (hU : U ⊆ dom (ident : Operator X bot)) (hne : U.Nonempty) :
    eye ∈ CoLip d (ident : Operator X bot) U := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  simp [ident]

end
end HCH02
