import formal_oet.vol_03.ch_13_comparison_and_falsification
import formal_oet.vol_01.ch_05_operator_networks.path_matrix
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_03.ch_14_empirical_network_fitting

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_02.ch_07_fitting_foundations
open formal_oet.vol_03.ch_12_residuals_and_substitution

open scoped BigOperators

variable {X I V : Type} {bot : X} [Fintype I]

/--
OET anchor: h-55c4fe8427039cfc
**定义（路径采样集）**
The component sample restricted to one reachable proxy-network path.
-/
def path_component_sample
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) (j : I) : Set X :=
  sample j ∩ N.path_domain q.nodes

/--
OET anchor: h-55c4fe8427039cfc
**定义（路径采样族）**
The componentwise sample family obtained by restricting every component sample
to a fixed reachable path.
-/
def path_sample_family
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) : I → Set X :=
  fun j => path_component_sample N sample q j

/--
OET anchor: h-55c4fe8427039cfc
**定义（路径可评估分量）**
The components whose path-restricted sample is nonempty.
-/
def path_evaluable_components
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) : Set I :=
  evaluable_components (path_sample_family N sample q)

/--
OET anchor: h-55c4fe8427039cfc
**定义（路径可评估分量，展开形式）**
A component is path-evaluable exactly when its path-restricted sample is
nonempty.
-/
theorem mem_path_evaluable_components_iff
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) (j : I) :
    j ∈ path_evaluable_components N sample q ↔
      (path_component_sample N sample q j).Nonempty := by
  rfl

/--
OET anchor: h-55c4fe8427039cfc
**定义（路径可评估分量，反面）**
If a component is not path-evaluable, there is no common anchor on that path
for that component.
-/
theorem not_path_evaluable_no_path_anchor
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) (j : I)
    (hj : j ∉ path_evaluable_components N sample q) :
    ¬ ∃ xs : X, xs ∈ path_component_sample N sample q j := by
  intro h
  exact hj h

/--
OET anchor: h-55c4fe8427039cfc
**定义（路径可评估分量，空路径采样）**
Non-evaluability on a path is equivalent to emptiness of the path-restricted
component sample.
-/
theorem path_component_sample_eq_empty_of_not_evaluable
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) (j : I)
    (hj : j ∉ path_evaluable_components N sample q) :
    path_component_sample N sample q j = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (hj ⟨x, hx⟩)
  · intro hx
    exact False.elim hx

/--
OET anchor: h-55c4fe8427039cfc
**定义（路径可评估分量，全局可评估性）**
Path evaluability implies global evaluability of the same component.
-/
theorem path_evaluable_subset_evaluable_components
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) :
    path_evaluable_components N sample q ⊆ evaluable_components sample := by
  intro j hj
  rcases hj with ⟨x, hx⟩
  exact ⟨x, hx.1⟩

/--
OET anchor: h-55c4fe8427039cfc
**定义（当前代理路径）**
The reachable proxy-network path determined by a point in the network source.
-/
def reachable_path_at
    (N : FiniteOperatorNetwork X bot V) {x : X} (hxU : x ∈ N.U) : N.ReachablePath :=
  ⟨N.path_of ⟨x, hxU⟩, ⟨x, hxU, rfl⟩⟩

/--
OET anchor: h-55c4fe8427039cfc
**定义（当前代理路径，路径域成员）**
A source point belongs to the path domain of its own reachable path.
-/
theorem mem_path_domain_reachable_path_at
    (N : FiniteOperatorNetwork X bot V) {x : X} (hxU : x ∈ N.U) :
    x ∈ N.path_domain (reachable_path_at N hxU).nodes :=
  ⟨hxU, rfl⟩

/--
OET anchor: h-55c4fe8427039cfc
**定义（路径级经验残差上界）**
The sampled residual upper bound of the path chain against the target, with
the observation-resolution correction fixed at `h-6f9e054ce01ccfef`.
-/
noncomputable def path_empirical_residual_upper
    (d : I → X → X → ENNReal)
    (target : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath) (j : I) : ENNReal :=
  empirical_residual_upper d target (N.path_chain q.nodes)
    (path_sample_family N sample q) delta_o j

/--
OET anchor: h-55c4fe8427039cfc
**定义（路径采样集，包含关系）**
Each path-restricted component sample is contained in the original component
sample.
-/
theorem path_component_sample_subset_component
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) (j : I) :
    path_component_sample N sample q j ⊆ sample j := by
  intro x hx
  exact hx.1

/--
OET anchor: h-55c4fe8427039cfc
**定义（路径采样集，路径域包含关系）**
Each path-restricted component sample is contained in the path domain.
-/
theorem path_component_sample_subset_path_domain
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) (j : I) :
    path_component_sample N sample q j ⊆ N.path_domain q.nodes := by
  intro x hx
  exact hx.2

/--
OET anchor: h-ed8808b4cfd52216
**命题（路径采样分解）**
If a component sample lies in the network source domain, it is the union of its
path-restricted samples over all reachable paths.
-/
theorem component_sample_eq_iUnion_path_component_sample
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X) (j : I)
    (hsampleU : sample j ⊆ N.U) :
    sample j = ⋃ q : N.ReachablePath, path_component_sample N sample q j := by
  ext x
  constructor
  · intro hx
    let q : N.ReachablePath :=
      ⟨N.path_of ⟨x, hsampleU hx⟩, ⟨x, hsampleU hx, rfl⟩⟩
    exact Set.mem_iUnion.mpr ⟨q, hx, hsampleU hx, rfl⟩
  · intro hx
    rcases Set.mem_iUnion.mp hx with ⟨q, hxq⟩
    exact hxq.1

/--
OET anchor: h-ed8808b4cfd52216
**命题（路径采样分解，逐点路径见证）**
Every component sample point in the network source belongs to the restricted
sample of its own reachable path.
-/
theorem component_sample_mem_own_path_component_sample
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X) (j : I)
    {x : X} (hx : x ∈ sample j) (hxU : x ∈ N.U) :
    x ∈ path_component_sample N sample (reachable_path_at N hxU) j :=
  ⟨hx, mem_path_domain_reachable_path_at N hxU⟩

/--
OET anchor: h-ed8808b4cfd52216
**命题（路径采样分解，互斥形式）**
Different reachable path labels have disjoint path-restricted samples.
-/
theorem disjoint_path_component_sample_of_nodes_ne
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X) (j : I)
    {p q : N.ReachablePath} (hne : p.nodes ≠ q.nodes) :
    Disjoint (path_component_sample N sample p j)
      (path_component_sample N sample q j) := by
  rw [Set.disjoint_iff]
  intro x hx
  exact (Set.disjoint_iff.mp (N.disjoint_path_domain_of_ne hne)) ⟨hx.1.2, hx.2.2⟩

/--
OET anchor: h-ed8808b4cfd52216
**命题（路径采样分解，路径链等于代理）**
On a reachable path domain, the path chain is the represented proxy.
-/
theorem path_chain_eq_represented_proxy_on_path
    (N : FiniteOperatorNetwork X bot V) (proxy : Operator X bot)
    (q : N.ReachablePath) (hrep : N.represents proxy)
    {x : X} (hx : x ∈ N.path_domain q.nodes) :
    (N.path_chain q.nodes).func x = proxy.func x := by
  have hpath :
      N.extensional_operator.func x = (N.path_chain q.nodes).func x :=
    N.local_equivalent_extensional_path_chain q x hx
  have hproxy :
      N.extensional_operator.func x = proxy.func x :=
    hrep x (N.path_domain_subset_source hx)
  exact hpath.symm.trans hproxy

/--
OET anchor: h-ed8808b4cfd52216
**命题（路径采样分解，路径残差受全局残差控制）**
When the network represents the proxy, the raw path residual supremum is
bounded by the corresponding global raw sample residual supremum.
-/
theorem path_empirical_residual_raw_sup_le_global
    (d : I → X → X → ENNReal)
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (q : N.ReachablePath) (j : I)
    (hrep : N.represents proxy) :
    empirical_residual_raw_sup d target (N.path_chain q.nodes)
      (path_component_sample N sample q j) j ≤
      empirical_residual_raw_sup d target proxy (sample j) j := by
  unfold empirical_residual_raw_sup
  apply iSup_le
  intro x
  have hchain :
      (N.path_chain q.nodes).func x.1 = proxy.func x.1 :=
    path_chain_eq_represented_proxy_on_path N proxy q hrep x.2.2
  simpa [hchain] using
    (le_iSup
      (fun y : {y // y ∈ sample j} =>
        d j (proxy.func y.1) (target.func y.1))
      ⟨x.1, x.2.1⟩)

/--
OET anchor: h-ed8808b4cfd52216
**命题（路径采样分解，路径经验残差上界）**
The path empirical residual upper bound is bounded by the global empirical
residual upper bound with the same observation correction.
-/
theorem path_empirical_residual_upper_le_global
    (d : I → X → X → ENNReal)
    (target proxy : Operator X bot)
    (N : FiniteOperatorNetwork X bot V) (sample : I → Set X)
    (delta_o : I → ENNReal) (q : N.ReachablePath) (j : I)
    (hrep : N.represents proxy) :
    path_empirical_residual_upper d target N sample delta_o q j ≤
      empirical_residual_upper d target proxy sample delta_o j := by
  unfold path_empirical_residual_upper empirical_residual_upper path_sample_family
  exact add_le_add
    (path_empirical_residual_raw_sup_le_global d target proxy N sample q j hrep)
    le_rfl

end formal_oet.vol_03.ch_14_empirical_network_fitting
