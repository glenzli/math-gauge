import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_01_foundations.metric_entropy

/-! Formalization of Chapter 3 of The Operator Evolution Theory by Zhe Li
(Glen Li / glenzli), ORCID 0009-0006-6536-3453, https://glenzli.com/books/oet/,
https://gitlab.com/glenzli/oet-public, CC BY 4.0, https://creativecommons.org/licenses/by/4.0/.
The chapter statements and examples are reformulated in Lean. -/
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

abbrev D (X : Type) := X → X → ENNReal
abbrev Op (b : X) := Operator X b

def Const (p : D X) (f : X → X) (U : Set X) :=
  ∀ x ∈ U, ∀ y ∈ U, p (f x) (f y) = 0

def Ident (p : D X) (f : X → X) (U : Set X) :=
  ¬ Const p f U ∧ ∀ x ∈ U, p (f x) x = 0

def Active (p : D X) (f : X → X) (U : Set X) :=
  ¬ Const p f U ∧ ¬ Ident p f U

theorem partition {p : D X} {f : X → X} {U : Set X} :
    (Const p f U ∧ ¬ Ident p f U ∧ ¬ Active p f U) ∨
    (Ident p f U ∧ ¬ Const p f U ∧ ¬ Active p f U) ∨
    (Active p f U ∧ ¬ Const p f U ∧ ¬ Ident p f U) := by
  unfold Ident Active
  tauto

variable {d : I → D X} {p : D X} {f g : X → X} {U : Set X}
variable {x y z w : X}

theorem zero_left (h : ExtendedPseudoMetric X b p) (hz : p x y = 0) :
    p x z = p y z := by
  apply le_antisymm
  · simpa [hz] using h.triangle x y z
  · simpa [h.symm y x, hz] using h.triangle y x z

theorem zero_right (h : ExtendedPseudoMetric X b p) (hz : p x y = 0) :
    p z x = p z y := by rw [h.symm z x, h.symm z y, zero_left h hz]

theorem zero_row [Fintype I] {i : I} (hc : Const (d i) f U) (hx : x ∈ U) (hy : y ∈ U) :
    d i (f x) (f y) ≤ ∑ k, (0 : ENNReal) * d k x y := by simp [hc x hx y hy]

theorem zero_entry [Fintype I] {F : Op b} {k i : I} {K : I → I → ENNReal}
    (hc : Const (d i) F.func U) (hK : IsCoLipMatrix d F U K)
    (hp : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨x,hx,y,hy,h⟩ := hp
  exact colip_entry_eq_zero_of_output_zero_input_pos d F U K k i x y hK hx hy (hc x hx y hy) h

theorem ident_dist (h : ExtendedPseudoMetric X b p) (hi : Ident p f U)
    (hx : x ∈ U) (hy : y ∈ U) : p (f x) (f y) = p x y :=
  (zero_left h (hi.2 x hx)).trans (zero_right h (hi.2 y hy))

theorem outer_const (hc : Const p g (f '' U)) : Const p (g ∘ f) U :=
  fun x hx y hy => hc _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩

theorem comp_ident (h : ExtendedPseudoMetric X b p) (h₁ : Ident p f U)
    (h₂ : Ident p g (f '' U)) : Ident p (g ∘ f) U := by
  constructor
  · intro hc
    apply h₁.1
    intro x hx y hy
    exact (ident_dist h h₂ (mem_image_of_mem f hx) (mem_image_of_mem f hy)).symm.trans (hc x hx y hy)
  · intro x hx
    exact (zero_left h (h₂.2 _ ⟨x,hx,rfl⟩)).trans (h₁.2 x hx)

theorem comp_active (h : ExtendedPseudoMetric X b p) (ha : Active p (g ∘ f) U) :
    Active p f U ∨ Active p g (f '' U) := by
  by_contra! hn
  have hg : ¬ Const p g (f '' U) := fun hc => ha.1 (outer_const hc)
  have hi : Ident p g (f '' U) := by by_contra hh; exact hn.2 ⟨hg,hh⟩
  have hf : ¬ Const p f U := by
    intro hc
    apply ha.1
    exact fun x hx y hy => (ident_dist h hi (mem_image_of_mem f hx)
      (mem_image_of_mem f hy)).trans (hc x hx y hy)
  apply hn.1
  exact ⟨hf, fun hh => ha.2 (comp_ident h hh hi)⟩

def stepActive (p : D X) : List (Op b) → Set X → Prop
  | [], _ => False
  | F :: tail, A => Active p F.func A ∨ stepActive p tail (F.func '' A)

theorem chain_active (h : ExtendedPseudoMetric X b p) (fs : List (Op b)) :
    Active p (OperatorChain fs.reverse).func U → stepActive p fs U := by
  induction fs generalizing U with
  | nil =>
    intro ha
    exact ha.2 ⟨ha.1, fun x _ => h.dist_self x⟩
  | cons F fs ih =>
    rw [List.reverse_cons, operator_chain_eq_prod, List.prod_append, List.prod_singleton,
      ← operator_chain_eq_prod]
    intro ha
    exact (comp_active (f := F.func) (g := (OperatorChain fs.reverse).func) h ha).imp_right ih

theorem diag_const [Fintype I] {F G : Op b} {L : I → I → ENNReal} {j : I}
    (hc : Const (d j) F.func U) (hl : IsLipMatrix d G (F.func '' U) L)
    (row : ∀ k, k ≠ j → L k j = 0) : Const (d j) (G.func ∘ F.func) U := by
  intro x hx y hy
  have hh := lip_bound_of_single_input_row d G _ L j j hl row _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  simpa [hc x hx y hy] using hh

def fiber (p : D X) (f : X → X) (U : Set X) (z : X) := {x ∈ U | p (f x) z = 0}
abbrev subD := @subfamily_pseudometric
theorem sub_zero {J : Set I} : subD d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  simp [subD, subfamily_pseudometric, ENNReal.iSup_eq_zero]

theorem fiber_target (h : ExtendedPseudoMetric X b p) (hz : p z w = 0) :
    fiber p f U z = fiber p f U w := by ext x; simp [fiber,zero_right h hz]

def blocks (p : D X) (f : X → X) (U : Set X) := fiber p f U '' (f '' U)

theorem fiber_cover (h : ExtendedPseudoMetric X b p) :
    (∀ S ∈ blocks p f U, Set.Nonempty S) ∧ ⋃₀ (blocks p f U) = U := by
  constructor
  · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,h.dist_self _⟩
  · ext x
    constructor
    · rintro ⟨_,⟨z,hz,rfl⟩,hx⟩
      exact hx.1
    · intro hx
      exact ⟨_, ⟨_,⟨x,hx,rfl⟩,rfl⟩,hx,h.dist_self _⟩

theorem fiber_disjoint (h : ExtendedPseudoMetric X b p) :
    fiber p f U z = fiber p f U w ∨ Disjoint (fiber p f U z) (fiber p f U w) := by
  by_cases hd : Disjoint (fiber p f U z) (fiber p f U w)
  · exact Or.inr hd
  obtain ⟨a,ha,ha'⟩ := Set.not_disjoint_iff.mp hd
  exact Or.inl (fiber_target h ((zero_left h ha.2).symm.trans ha'.2))

theorem fiber_inter {J : Set I} (hj : J.Nonempty) :
    fiber (subD d J) f U z = ⋂ j ∈ J, fiber (d j) f U z := by
  obtain ⟨i,hi⟩ := hj
  ext x
  simp only [fiber, mem_setOf_eq, sub_zero, mem_iInter]
  grind

theorem fiber_anti {J K : Set I} (h : J ⊆ K) :
    fiber (subD d K) f U z ⊆ fiber (subD d J) f U z :=
  fun _ hx => ⟨hx.1,sub_zero.mpr fun j hj => sub_zero.mp hx.2 j (h hj)⟩

theorem fiber_edges (i : I) :
    fiber (subD d {i}) f U z = fiber (d i) f U z ∧
    fiber (subD d univ) f U z ⊆ fiber (d i) f U z :=
  ⟨by simp [subD, subfamily_pseudometric_singleton], fun _ hx => ⟨hx.1, sub_zero.mp hx.2 i trivial⟩⟩

theorem fiber_ident (h : ExtendedPseudoMetric X b p) (hi : Ident p f U) :
    fiber p f U z = {x ∈ U | p x z = 0} := by
  ext x
  exact and_congr_right fun hx => by rw [zero_left h (hi.2 x hx)]

theorem fiber_const (h : ExtendedPseudoMetric X b p) (hc : Const p f U) (hz : z ∈ f '' U) :
    fiber p f U z = U ∧ (0 < p w z → fiber p f U w = ∅) := by
  obtain ⟨y,hy,rfl⟩ := hz
  constructor
  · exact Set.Subset.antisymm (fun _ hx => hx.1) (fun x hx => ⟨hx,hc x hx y hy⟩)
  · intro hp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hp.ne' ((zero_left h hx.2).symm.trans (hc x hx.1 y hy))

end
end C3
