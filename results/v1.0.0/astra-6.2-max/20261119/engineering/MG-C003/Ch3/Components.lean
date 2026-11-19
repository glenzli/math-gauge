import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import formal_oet.vol_01.ch_02_operator_bounds.single_channel

/-! Chapter 3 of Zhe Li (Glen Li / glenzli), *The Operator Evolution Theory*.
New Lean formalization, CC BY 4.0. https://glenzli.com/books/oet/ -/
namespace MG
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {b : X}
abbrev Op (b : X) := Operator X b
abbrev Dist (X : Type) := X → X → ENNReal
variable {p : Dist X} {f g : Op b} {U : Set X} {x y z : X}

def Const (p : Dist X) (f : Op b) (U : Set X) := ∀ x ∈ U, ∀ y ∈ U, p (f.func x) (f.func y) = 0
def Ident (p : Dist X) (f : Op b) (U : Set X) := ¬ Const p f U ∧ ∀ x ∈ U, p (f.func x) x = 0
def Active (p : Dist X) (f : Op b) (U : Set X) := ¬ Const p f U ∧ ¬ Ident p f U

theorem partition : (Const p f U ∨ Ident p f U ∨ Active p f U) ∧
    ¬ (Const p f U ∧ Ident p f U) ∧ ¬ (Const p f U ∧ Active p f U) ∧
    ¬ (Ident p f U ∧ Active p f U) := by unfold Active Ident; tauto

theorem zeroRow [Fintype I] (d : I → Dist X) (i : I) (h : Const (d i) f U)
    (hx : x ∈ U) (hy : y ∈ U) :
    d i (f.func x) (f.func y) ≤ ∑ k, 0 * d k x y ∧ (∑ k, 0 * d k x y) = 0 := by
  simp [h x hx y hy]

theorem zeroEntry [Fintype I] (d : I → Dist X) (K : I → I → ENNReal) (i k : I)
    (hc : Const (d i) f U) (hK : IsCoLipMatrix d f U K)
    (h : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k i = 0 := by
  obtain ⟨a, ha, c, hc', hp⟩ := h
  exact colip_entry_eq_zero_of_output_zero_input_pos d f U K k i a c hK ha hc' (hc _ ha _ hc') hp

theorem zeroLeft (m : ExtendedPseudoMetric X b p) (h : p x y = 0) : p x z = p y z := by
  apply le_antisymm
  · simpa [h] using m.triangle x y z
  · simpa [m.symm y x, h] using m.triangle y x z

theorem zeroRight (m : ExtendedPseudoMetric X b p) (h : p y z = 0) : p x y = p x z := by
  rw [m.symm x y, m.symm x z, zeroLeft m h]

theorem identDist (m : ExtendedPseudoMetric X b p) (h : Ident p f U) (hx : x ∈ U) (hy : y ∈ U) :
    p (f.func x) (f.func y) = p x y :=
  (zeroLeft m (h.2 _ hx)).trans (zeroRight m (h.2 _ hy))

theorem outerConst (h : Const p g (f.func '' U)) : Const p (g * f) U :=
  fun x hx y hy => h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩

theorem compIdent (m : ExtendedPseudoMetric X b p) (hf : Ident p f U)
    (hg : Ident p g (f.func '' U)) : Ident p (g * f) U := by
  constructor
  · intro hc
    apply hf.1
    intro x hx y hy
    rw [← identDist m hg (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)]
    exact hc _ hx _ hy
  · intro x hx
    change p (g.func (f.func x)) x = 0
    rw [zeroLeft m (hg.2 _ ⟨x,hx,rfl⟩), hf.2 _ hx]

theorem compActive (m : ExtendedPseudoMetric X b p) (h : Active p (g * f) U) :
    Active p f U ∨ Active p g (f.func '' U) := by
  by_contra! hn
  rcases partition (p := p) (f := g) (U := f.func '' U) |>.1 with hc | hi | ha
  · exact h.1 (outerConst hc)
  · rcases partition (p := p) (f := f) (U := U) |>.1 with c | i | a
    · apply h.1
      intro x hx y hy
      exact (identDist m hi (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)).trans (c _ hx _ hy)
    · exact h.2 (compIdent m i hi)
    · exact hn.1 a
  · exact hn.2 ha

def chain : List (Op b) → Op b
  | [] => 1
  | f :: fs => chain fs * f

def stepActive (p : Dist X) : List (Op b) → Set X → Prop
  | [], _ => False
  | f :: fs, U => Active p f U ∨ stepActive p fs (f.func '' U)

theorem chain_order (fs : List (Op b)) : chain fs = OperatorChain fs.reverse := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [chain, ih, operator_chain_eq_prod]

theorem chain_domain (fs : List (Op b)) (h : U ⊆ dom (chain (f :: fs))) :
    U ⊆ dom f ∧ f.func '' U ⊆ dom (chain fs) := by
  constructor
  · intro x hx hb
    apply h hx
    change (chain fs).func (f.func x) = b
    rw [hb, (chain fs).preserves_bot]
  · rintro _ ⟨x,hx,rfl⟩
    exact h hx

theorem emptyActive (m : ExtendedPseudoMetric X b p) : ¬ Active p (1 : Op b) U :=
  fun h => h.2 ⟨h.1, fun x _ => m.dist_self x⟩

theorem chainActive (m : ExtendedPseudoMetric X b p) (fs : List (Op b))
    (hU : U ⊆ dom (chain fs)) (h : Active p (chain fs) U) : stepActive p fs U := by
  induction fs generalizing U with
  | nil => exact (emptyActive m h).elim
  | cons f fs ih =>
    rcases compActive m (g := chain fs) (f := f) h with a | a
    · exact Or.inl a
    · exact Or.inr (ih (chain_domain fs hU).2 a)

theorem diagConst [Fintype I] (d : I → Dist X) (j : I) (L : I → I → ENNReal)
    (hf : Const (d j) f U) (hg : IsLipMatrix d g (f.func '' U) L)
    (row : ∀ k, k ≠ j → L k j = 0) : Const (d j) (g * f) U := by
  intro x hx y hy
  apply le_antisymm _ bot_le
  simpa [hf x hx y hy] using lip_bound_of_single_input_row d g _ L j j hg row
    _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)

def fiber (p : Dist X) (f : Op b) (U : Set X) (y : X) : Set X := {x | x ∈ U ∧ p (f.func x) y = 0}
noncomputable abbrev subdist := @subfamily_pseudometric
def blocks (p : Dist X) (f : Op b) (U : Set X) : Set (Set X) := fiber p f U '' (f.func '' U)

theorem subzero (d : I → Dist X) (J : Set I) :
    subdist d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  change (⨆ j : J, d j.val x y) = 0 ↔ _
  simp [Subtype.forall]

theorem fiberTarget (m : ExtendedPseudoMetric X b p) (h : p y z = 0) :
    fiber p f U y = fiber p f U z := by ext a; simp [fiber, zeroRight m h]

theorem fiberCover (m : ExtendedPseudoMetric X b p) :
    (∀ F ∈ blocks p f U, F.Nonempty) ∧ ⋃₀ (blocks p f U) = U := by
  constructor
  · rintro _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,m.dist_self _⟩
  · ext x
    constructor
    · rintro ⟨_,⟨y,_,rfl⟩,hx⟩
      exact hx.1
    · intro hx
      exact ⟨_, ⟨_,⟨x,hx,rfl⟩,rfl⟩, hx, m.dist_self _⟩

theorem fiberPartition (m : ExtendedPseudoMetric X b p) {F G : Set X} (hF : F ∈ blocks p f U) (hG : G ∈ blocks p f U) :
    F = G ∨ Disjoint F G := by
  obtain ⟨y,_,rfl⟩ := hF
  obtain ⟨z,_,rfl⟩ := hG
  by_cases h : Disjoint (fiber p f U y) (fiber p f U z)
  · exact Or.inr h
  · obtain ⟨x,hx,hx'⟩ := Set.not_disjoint_iff.mp h
    exact Or.inl (fiberTarget m ((zeroLeft m hx.2).symm.trans hx'.2))

theorem fiberInter (d : I → Dist X) {J : Set I} (hJ : J.Nonempty) :
    fiber (subdist d J) f U y = ⋂ j ∈ J, fiber (d j) f U y := by
  ext x
  simp only [fiber, mem_setOf_eq, subzero, mem_iInter]
  obtain ⟨j,hj⟩ := hJ
  exact ⟨fun h i hi => ⟨h.1,h.2 i hi⟩, fun h => ⟨(h j hj).1, fun i hi => (h i hi).2⟩⟩

theorem fiberAnti (d : I → Dist X) {J K : Set I} (h : J ⊆ K) :
    fiber (subdist d K) f U y ⊆ fiber (subdist d J) f U y :=
  fun _ hx => ⟨hx.1,(subzero d J).2 fun j hj => (subzero d K).1 hx.2 j (h hj)⟩

theorem fiberEnds (d : I → Dist X) (i : I) :
    fiber (subdist d {i}) f U y = {x ∈ U | d i (f.func x) y = 0} ∧
    fiber (subdist d univ) f U y ⊆ fiber (d i) f U y := by
  rw [show subdist d {i} = d i from subfamily_pseudometric_singleton d i]
  exact ⟨rfl, fun x hx => ⟨hx.1,(subzero d univ).1 hx.2 i trivial⟩⟩

theorem identFiber (m : ExtendedPseudoMetric X b p) (hi : Ident p f U) :
    fiber p f U y = {x ∈ U | p x y = 0} := by
  ext x
  exact and_congr_right fun hx => by rw [zeroLeft m (hi.2 x hx)]

theorem constFiber (m : ExtendedPseudoMetric X b p) (hc : Const p f U) (hy : y ∈ f.func '' U) :
    fiber p f U y = U ∧ ∀ z, 0 < p z y → fiber p f U z = ∅ := by
  obtain ⟨a,ha,rfl⟩ := hy
  constructor
  · ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx,hc _ hx _ ha⟩⟩
  · intro z hz
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hz.ne' ((zeroLeft m hx.2).symm.trans (hc _ hx.1 _ ha))

end MG
