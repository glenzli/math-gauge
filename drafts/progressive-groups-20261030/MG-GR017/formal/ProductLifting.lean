import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Tactic

noncomputable section
open Set Filter Function Topology
namespace MathGauge.ProductLifting
universe u v w

/-- The actual lifting property, quantified over compact Hausdorff source and target spaces. -/
def Lifts (P : Type u) [TopologicalSpace P] : Prop :=
  ∀ (Y : Type v) (Z : Type w) [TopologicalSpace Y] [TopologicalSpace Z]
    [CompactSpace Y] [T2Space Y] [TotallyDisconnectedSpace Y]
    [CompactSpace Z] [T2Space Z] [TotallyDisconnectedSpace Z]
    (q : Y → Z) (f : P → Z), Continuous q → Surjective q → Continuous f →
      ∃ g : P → Y, Continuous g ∧ q ∘ g = f

/-- Arbitrary lifts on the discrete principal points extend and agree by density. -/
theorem ultrafilter_lifts (A : Type u) : Lifts.{u,v,w} (Ultrafilter A) := by
  intro Y Z _ _ _ _ _ _ _ _ q f hq hqs hf
  obtain ⟨s, hs⟩ := hqs.hasRightInverse
  let g := Ultrafilter.extend (s ∘ f ∘ (pure : A → Ultrafilter A))
  refine ⟨g, continuous_ultrafilter_extend _, ?_⟩
  apply denseRange_pure.equalizer (hq.comp (continuous_ultrafilter_extend _)) hf
  funext a
  simp only [comp_apply, ultrafilter_extend_pure]
  exact hs (f (pure a))

abbrev P := Ultrafilter ℕ
abbrev B := P × P

/-- All topological assumptions on the actual two factors. -/
theorem factor_profinite : CompactSpace P ∧ T2Space P ∧ TotallyDisconnectedSpace P :=
  ⟨inferInstance,inferInstance,inferInstance⟩

def diagonalPoints : Set B := range fun n : ℕ => (pure n, pure n)
def diagonal : Set B := {z | z.1 = z.2}

theorem pure_singleton_open (n : ℕ) : IsOpen ({pure n} : Set P) := by
  have h : ({pure n} : Set P) = {u | ({n} : Set ℕ) ∈ u} := by
    ext u
    simp only [mem_singleton_iff, mem_setOf_eq]
    rw [← Ultrafilter.coe_le_coe, Ultrafilter.coe_pure, Filter.le_pure_iff]
    rfl
  rw [h]
  exact ultrafilter_isOpen_basic _

theorem diagonalPoints_open : IsOpen diagonalPoints := by
  have h : diagonalPoints = ⋃ n : ℕ, ({pure n} : Set P) ×ˢ ({pure n} : Set P) := by
    ext z
    simp only [diagonalPoints, mem_range, mem_iUnion, mem_prod, mem_singleton_iff]
    constructor
    · rintro ⟨n, rfl⟩; exact ⟨n, rfl, rfl⟩
    · rintro ⟨n, h₁, h₂⟩; exact ⟨n, Prod.ext h₁.symm h₂.symm⟩
  rw [h]
  exact isOpen_iUnion fun n => (pure_singleton_open n).prod (pure_singleton_open n)

theorem closure_diagonalPoints : closure diagonalPoints = diagonal := by
  apply le_antisymm
  · apply closure_minimal
    · rintro _ ⟨n, rfl⟩; rfl
    · exact isClosed_eq continuous_fst continuous_snd
  · rintro ⟨u,v⟩ (h : u = v)
    subst v
    have hmem := mem_closure_image
      (show ContinuousAt (fun x : P => (x,x)) u from
        (continuous_id.prodMk continuous_id).continuousAt) (denseRange_pure u)
    convert hmem using 1
    rw [← Set.range_comp]
    rfl

theorem diagonal_not_open : ¬ IsOpen diagonal := by
  intro h
  have hs : ∀ u : P, IsOpen ({u} : Set P) := by
    intro u
    have hc : Continuous (fun v : P => (v,u)) := continuous_id.prodMk continuous_const
    convert h.preimage hc using 1
  letI : DiscreteTopology P := ⟨eq_bot_of_singletons_open hs⟩
  letI : Finite P := finite_of_compact_of_discrete
  haveI : Finite ℕ := Finite.of_injective (pure : ℕ → P) Ultrafilter.pure_injective
  exact not_finite ℕ

theorem product_not_extremallyDisconnected : ¬ ExtremallyDisconnected B := by
  intro h
  have := h.open_closure diagonalPoints diagonalPoints_open
  rw [closure_diagonalPoints] at this
  exact diagonal_not_open this

/-- A concrete two-sheeted closed cover of the product. -/
def coverSet : Set (B × Bool) :=
  (diagonalPointsᶜ ×ˢ {true}) ∪ (diagonal ×ˢ {false})
abbrev Cover := coverSet

theorem coverSet_closed : IsClosed coverSet :=
  (diagonalPoints_open.isClosed_compl.prod isClosed_singleton).union
    ((isClosed_eq continuous_fst continuous_snd).prod isClosed_singleton)

instance : CompactSpace Cover := isCompact_iff_compactSpace.mp coverSet_closed.isCompact
instance : T2Space Cover := inferInstance
instance : TotallyDisconnectedSpace Cover := inferInstance

def coverMap (z : Cover) : B := z.val.1

theorem coverMap_continuous : Continuous coverMap := continuous_fst.comp continuous_subtype_val

theorem coverMap_surjective : Surjective coverMap := by
  intro z
  by_cases hz : z ∈ diagonalPoints
  · refine ⟨⟨(z,false), Or.inr ⟨?_, rfl⟩⟩, rfl⟩
    rw [← closure_diagonalPoints]
    exact subset_closure hz
  · exact ⟨⟨(z,true), Or.inl ⟨hz,rfl⟩⟩, rfl⟩

/-- No continuous section exists; the false-sheet preimage would make the diagonal open. -/
theorem coverMap_no_section : ¬ ∃ s : B → Cover, Continuous s ∧ coverMap ∘ s = id := by
  rintro ⟨s,hs,hsec⟩
  let c : B → Bool := fun z => (s z).val.2
  have hc : Continuous c := continuous_snd.comp (continuous_subtype_val.comp hs)
  have first (z : B) : (s z).val.1 = z := congr_fun hsec z
  have hon : diagonalPoints ⊆ c ⁻¹' {false} := by
    intro z hz
    rcases (s z).property with h | h
    · exact ((first z ▸ h.1) hz).elim
    · exact h.2
  have hcclosed : IsClosed (c ⁻¹' {false}) := isClosed_singleton.preimage hc
  have hin : diagonal ⊆ c ⁻¹' {false} := by
    rw [← closure_diagonalPoints]
    exact closure_minimal hon hcclosed
  have hout : c ⁻¹' {false} ⊆ diagonal := by
    intro z hz
    rcases (s z).property with h | h
    · have : (true : Bool) = false := h.2.symm.trans hz
      cases this
    · exact first z ▸ h.1
  have heq : diagonal = c ⁻¹' {false} := Subset.antisymm hin hout
  apply diagonal_not_open
  rw [heq]
  exact (isOpen_discrete ({false} : Set Bool)).preimage hc

/-- Both factors satisfy the exact stated profinite lifting property, while the displayed
profinite cover of their product is continuous, onto and has no continuous section. -/
theorem counterexample :
    Lifts.{0,v,w} P ∧ Continuous coverMap ∧ Surjective coverMap ∧
      (¬ ∃ s : B → Cover, Continuous s ∧ coverMap ∘ s = id) :=
  ⟨ultrafilter_lifts ℕ, coverMap_continuous, coverMap_surjective, coverMap_no_section⟩

theorem product_not_lifts : ¬ Lifts.{0,0,0} B := by
  intro h
  exact coverMap_no_section
    (h Cover B coverMap id coverMap_continuous coverMap_surjective continuous_id)

end MathGauge.ProductLifting
