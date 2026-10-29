import Construction

open scoped Topology
open TopologicalSpace

namespace MathGauge.F104

universe u v w z

variable {ι : Type u} {X : Type v} {Y : ι → Type w}

/-- 证明构造的拓扑确实使得全部映射 $f_i$ 连续。 -/
theorem candidate_realizes (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    Realizes t f (assembled t f) := by
  intro i
  letI : TopologicalSpace X := assembled t f
  letI : TopologicalSpace (Y i) := t i
  rw [continuous_iff_le_induced]
  exact iInf_le (fun j => TopologicalSpace.induced (f j) (t j)) i

/-- 映射性质的充分性（前向）：若 $g$ 连续，则各复合 $f_i \circ g$ 均连续。 -/
theorem candidate_inbound (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {Z : Type z} (s : TopologicalSpace Z) (g : Z → X)
    (hg : Continuous[s, assembled t f] g) :
    ∀ i, Continuous[s, t i] (f i ∘ g) := by
  intro i
  letI : TopologicalSpace Z := s
  letI : TopologicalSpace X := assembled t f
  letI : TopologicalSpace (Y i) := t i
  exact (candidate_realizes t f i).comp hg

/-- 映射性质的必要性（反向）：若各复合 $f_i \circ g$ 均连续，则 $g$ 连续。 -/
theorem candidate_outbound (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {Z : Type z} (s : TopologicalSpace Z) (g : Z → X)
    (hg : ∀ i, Continuous[s, t i] (f i ∘ g)) :
    Continuous[s, assembled t f] g := by
  letI : TopologicalSpace Z := s
  letI : TopologicalSpace X := assembled t f
  rw [continuous_iff_le_induced]
  show s ≤ TopologicalSpace.induced g (assembled t f)
  dsimp only [assembled]
  rw [TopologicalSpace.induced_iInf]
  apply le_iInf
  intro i
  have h_comp := (TopologicalSpace.induced_compose g (f i) (t i)).symm
  rw [h_comp]
  letI : TopologicalSpace (Y i) := t i
  exact continuous_iff_le_induced.mp (hg i)

/-- 正文映射性质（充要条件）：
$g : (Z,\sigma) \to (X,\tau)$ 连续，当且仅当每个 $f_i \circ g : (Z,\sigma) \to (Y_i,\tau_i)$ 连续。 -/
theorem mapping_property (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {Z : Type z} (s : TopologicalSpace Z) (g : Z → X) :
    Continuous[s, assembled t f] g ↔ ∀ i, Continuous[s, t i] (f i ∘ g) :=
  ⟨candidate_inbound t f s g, candidate_outbound t f s g⟩

/-- 最粗拓扑的形式化谓词：使得全部映射连续，且比任意其它使其全部连续的拓扑都粗。 -/
def IsCoarsest (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    (s : TopologicalSpace X) : Prop :=
  Realizes t f s ∧ ∀ s', Realizes t f s' → s' ≤ s

/-- 证明构造的拓扑是使全部 $f_i$ 连续的最粗拓扑。 -/
theorem assembled_isCoarsest (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i) :
    IsCoarsest t f (assembled t f) :=
  ⟨candidate_realizes t f, fun s hs => construction_bound t f s hs⟩

/-- 证明使全部 $f_i$ 连续的最粗拓扑唯一。 -/
theorem coarsest_unique (t : ∀ i, TopologicalSpace (Y i)) (f : ∀ i, X → Y i)
    {s₁ s₂ : TopologicalSpace X} (h₁ : IsCoarsest t f s₁) (h₂ : IsCoarsest t f s₂) :
    s₁ = s₂ :=
  le_antisymm (h₂.2 s₁ h₁.1) (h₁.2 s₂ h₂.1)

#print axioms candidate_realizes
#print axioms candidate_inbound
#print axioms candidate_outbound
#print axioms mapping_property
#print axioms coarsest_unique

end MathGauge.F104
