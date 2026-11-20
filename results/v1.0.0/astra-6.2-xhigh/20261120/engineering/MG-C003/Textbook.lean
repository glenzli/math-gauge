import Chapter

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
variable {X I : Type} {b : X} {d : I → D X} {U : Set X} {F G : Op b}

theorem row_constraints [Fintype I] (_hU : U ⊆ dom F) {i : I} (h : Const (d i) F.func U)
    (x : X) (hx : x ∈ U) (y : X) (hy : y ∈ U) :
    d i (F.func x) (F.func y) ≤ ∑ k, (0 : ENNReal)*d k x y ∧
    ∑ k, (0 : ENNReal)*d k x y = 0 :=
  ⟨zero_row h hx hy,by simp⟩

theorem composition_sets (hd : ∀ i, ExtendedPseudoMetric X b (d i)) (hU : U ⊆ dom (G*F)) :
    let C := components d (G*F) U hU
    let A := components d F U (comp_domains hU).1
    let B := components d G (F.func '' U) (comp_domains hU).2
    C.2.2 ⊆ A.2.2 ∪ B.2.2 ∧ A.2.1 ∩ B.2.1 ⊆ C.2.1 :=
  ⟨fun i hi => comp_active (f := F.func) (g := G.func) (hd i) hi,
   fun i hi => comp_ident (f := F.func) (g := G.func) (hd i) hi.1 hi.2⟩

theorem chain_sets (hd : ∀ i, ExtendedPseudoMetric X b (d i)) (fs : List (Op b))
    (hU : U ⊆ dom (OperatorChain fs.reverse)) :
    (components d (OperatorChain fs.reverse) U hU).2.2 ⊆
      ⋃ stage ∈ stages fs U, {i | Active (d i) stage.1.func stage.2} := by
  intro i hi
  obtain ⟨s,hs,h⟩ := (stages_spec fs (d i)).mp (chain_active (hd i) fs hi)
  exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨hs,h⟩⟩

def pointRadius (p q : D X) (F : Op b) (U : Set X) (_ : U ⊆ dom F) (y : U) :=
  rad p q F.func U y
def uniformRadius (p q : D X) (F : Op b) (A U : Set X) (_ : A.Nonempty)
    (_ : A ⊆ U) (_ : U ⊆ dom F) := uniform p q F.func A U

theorem radius_representations (p q : D X) {A : Set X} (ha : A.Nonempty) (h : A ⊆ U)
    (hU : U ⊆ dom F) :
    uniformRadius p q F A U ha h hU = ⨅ y : A, pointRadius p q F U hU ⟨y,h y.2⟩ := rfl

theorem matrix_composition (_hn : U.Nonempty) (_hU : U ⊆ dom (G*F)) (i j l : I) :
    ((∀ a ∈ F.func '' U, ∀ c ∈ F.func '' U, d l a c = 0 → d j (G.func a) (G.func c) = 0) →
       N d F.func U l i ≤ N d (G*F).func U j i) ∧
    (∀ L, PosFin L → (∀ x ∈ U, ∀ y ∈ U, d l (F.func x) (F.func y) ≤ L*d i x y) →
       N d G.func (F.func '' U) j l / L ≤ N d (G*F).func U j i) :=
  ⟨fun hz => comp_zero (f := F.func) (g := G.func) hz,
   fun _ hl h => comp_lip (f := F.func) (g := G.func) hl h⟩

theorem threshold_sets (S : Scale X I) (A : {A : Set X // A.Nonempty}) (_hA : A.val ⊆ dom F)
    {t u t' u' : ENNReal} (_ht : PosFin t) (_hu : PosFin u) (_ht' : PosFin t') (_hu' : PosFin u')
    (ht : t ≤ t') (hu : u ≤ u') :
    {ij : I × I | (channel S A d F.func t u ij.1 ij.2).1 = true} ⊆
      {ij | (channel S A d F.func t' u ij.1 ij.2).1 = true} ∧
    {ij : I × I | (channel S A d F.func t u' ij.1 ij.2).2 = true} ⊆
      {ij | (channel S A d F.func t u ij.1 ij.2).2 = true} :=
  ⟨fun _ => scale_threshold ht,fun _ => null_threshold hu⟩

theorem separation_witness (_hn : U.Nonempty) (_hU : U ⊆ dom F) (i j : I) {τ : ENNReal}
    (_ht : PosFin τ) (_small : N d F.func U j i < τ) (α : ENNReal) (_hα : PosFin α)
    (h₁ : N d F.func U j i < α) (_h₂ : α < τ) :
    ∃ x ∈ U, ∃ y ∈ U, ∃ ε, PosFin ε ∧ d i x y < α ∧ ε ≤ d j (F.func x) (F.func y) :=
  uniform_witness h₁

theorem cover_constraints (_hn : U.Nonempty) (_hU : U ⊆ dom F) (i j : I) {τ : ENNReal}
    (_ht : PosFin τ) (h : τ ≤ N d F.func U j i) {B : Set X} (hb : B ⊆ U) {ε : ENNReal}
    (he : PosFin ε) :
    (∀ x ∈ U, ball (d i) x τ ∩ U ⊆ fiber (d j) F.func U (F.func x)) ∧
    cov (d j) ε (F.func '' B) ≤ cov (d i) τ B ∧
    (B.Nonempty → ent (d j) ε (F.func '' B) ≤ ent (d i) τ B) :=
  ⟨fun _ hx => threshold_ball h hx,threshold_cover hb h he.1,fun _ => threshold_entropy hb h he.1⟩

theorem small_image (_hU : U ⊆ dom F) (hn : U.Nonempty) (i j : I) {t u : ENNReal}
    (_ht : PosFin t) (_hu : PosFin u) (h : diameter (d i) U < t) (hh : t ≤ u) :
    (u ≤ N d F.func U j i ↔ Const (d j) F.func U) ∧
    (u ≤ N d F.func U j i → ∀ e, PosFin e → cov (d j) e (F.func '' U) = 1) :=
  ⟨small_iff h hh,fun hr _ he => small_cover hn h hh hr he.1⟩

theorem distance_gap [Fintype I] {K : I → I → ENNReal} (hK : IsCoLipMatrix d F U K)
    {i j : I} (h : 0 < K i j) (hr : 0 < N d F.func U j i) :
    Disjoint ({0} : Set ENNReal) (Ici (N d F.func U j i)) ∧
    ∀ x ∈ U, ∀ y ∈ U, d i x y ∈ ({0} : Set ENNReal) ∪ Ici (N d F.func U j i) :=
  ⟨by simp [hr.not_ge],fun _ hx _ hy => uniform_gap hK h hx hy⟩

end
end C3
