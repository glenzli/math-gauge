import formal_oet.vol_02.ch_07_fitting_foundations.fitting_ball
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_02.ch_09_family_fitting

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_02.ch_07_fitting_foundations

open scoped BigOperators

noncomputable section

variable {X I β : Type} {bot : X}
variable (d : I → X → X → ENNReal)
variable [Fintype I] [Nonempty I] [Fintype β] [Nonempty β]

/--
OET anchor: h-16c45c5e0e60f572
**定义（活跃集）**
The active target indices at `x` relative to the ambient fitting domain `U`.
-/
def active_indices (target : β → Operator X bot) (U : Set X) (x : X) : Set β :=
  { b | x ∈ U ∧ x ∈ dom (target b) }

/--
OET anchor: h-16c45c5e0e60f572
**定义（目标重数）**
The cardinality of the active target set at a point.
-/
noncomputable def target_multiplicity [Fintype β]
    (target : β → Operator X bot) (U : Set X) (x : X) : Nat :=
  by
    classical
    exact (Finset.univ.filter fun b => b ∈ active_indices target U x).card

/--
OET anchor: h-16c45c5e0e60f572
**定义（有效族域）**
The points of `U` covered by at least one target operator.
-/
def effective_family_domain (target : β → Operator X bot) (U : Set X) : Set X :=
  { x | x ∈ U ∧ ∃ b : β, x ∈ dom (target b) }

/--
OET anchor: h-16c45c5e0e60f572
**定义（成对重叠域）**
The pairwise overlap domain of two target indices.
-/
def overlap_domain (target : β → Operator X bot) (U : Set X) (a b : β) : Set X :=
  effective_family_domain target U ∩ dom (target a) ∩ dom (target b)

/--
OET anchor: h-16c45c5e0e60f572
**定义（成对分歧向量）**
The `j` component of the pairwise divergence vector.
-/
def pairwise_divergence
    (target : β → Operator X bot) (a b : β) (x : X) (j : I) : ENNReal :=
  d j ((target a).func x) ((target b).func x)

/--
OET anchor: h-16c45c5e0e60f572
**定义（域级分歧上确界）**
The componentwise supremum of pairwise divergence on the overlap domain.
-/
noncomputable def domain_divergence
    (target : β → Operator X bot) (U : Set X) (a b : β) (j : I) : ENNReal :=
  ⨆ x : {x // x ∈ overlap_domain target U a b},
    pairwise_divergence d target a b x.1 j

/--
OET anchor: h-a9984fd2a088982a
**辅助定义（全族成对分歧上确界）**
The family-wide supremum of pairwise divergence used as a
selection-independent bound.
When there are no distinct pairs, the supremum over the empty subtype is `0`.
-/
noncomputable def family_pairwise_divergence_supremum
    (target : β → Operator X bot) (U : Set X) (j : I) : ENNReal :=
  ⨆ p : {p : β × β // p.1 ≠ p.2},
    domain_divergence d target U p.1.1 p.1.2 j

/--
OET anchor: h-68e510dbbcca4760
**定义（族成对分歧下界）**
One half of the supremal pairwise domain divergence.
-/
noncomputable def pairwise_tolerance_lower_bound
    (target : β → Operator X bot) (U : Set X) (j : I) : ENNReal :=
  family_pairwise_divergence_supremum d target U j / 2

/--
OET anchor: h-16c45c5e0e60f572
**定义（联合拟合）**
Pointwise all-component form of joint fitting for a target family.
-/
structure JointFitting
    [Fintype I] [Nonempty I]
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal) : Prop where
  tolerance_finite : ∀ j : I, eps j ≠ ⊤
  proxy_dom : effective_family_domain target U ⊆ dom proxy
  error :
    ∀ x ∈ effective_family_domain target U, ∀ b : β,
      b ∈ active_indices target U x → ∀ j : I,
        d j ((target b).func x) (proxy.func x) ≤ eps j

/-- Joint fitting restricts monotonically when the evaluation domain shrinks. -/
theorem joint_fitting_mono_domain
    {target : β → Operator X bot} {proxy : Operator X bot}
    {U V : Set X} {eps : I → ENNReal}
    (hsub : V ⊆ U) (hfit : JointFitting d target proxy U eps) :
    JointFitting d target proxy V eps := by
  refine ⟨hfit.tolerance_finite, ?_, ?_⟩
  · intro x hx
    exact hfit.proxy_dom ⟨hsub hx.1, hx.2⟩
  · intro x hx b hb j
    exact hfit.error x ⟨hsub hx.1, hx.2⟩ b ⟨hsub hb.1, hb.2⟩ j

/-- Joint fitting is monotone when every component tolerance is enlarged. -/
theorem joint_fitting_mono_tolerance
    {target : β → Operator X bot} {proxy : Operator X bot}
    {U : Set X} {eps eta : I → ENNReal}
    (heta_finite : ∀ j : I, eta j ≠ ⊤)
    (hle : ∀ j : I, eps j ≤ eta j)
    (hfit : JointFitting d target proxy U eps) :
    JointFitting d target proxy U eta := by
  refine ⟨heta_finite, hfit.proxy_dom, ?_⟩
  intro x hx b hb j
  exact le_trans (hfit.error x hx b hb j) (hle j)

/--
OET anchor: h-5519d2d2e212fbd6
**定义（活跃目标指标集）**
The indices whose restricted target domain on `U` is nonempty.
-/
def active_target_indices (target : β → Operator X bot) (U : Set X) : Set β :=
  {b | (U ∩ dom (target b)).Nonempty}

/--
OET anchor: h-5519d2d2e212fbd6
**定义（目标拟合集）**
The active target indices fitted by a proxy on their restricted domains.
-/
def target_fit_set
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal) : Set β :=
  {b | b ∈ active_target_indices target U ∧
    U ∩ dom (target b) ⊆ dom proxy ∧
    ∀ x ∈ U ∩ dom (target b), ∀ j : I,
      d j ((target b).func x) (proxy.func x) ≤ eps j}

/--
OET anchor: h-5519d2d2e212fbd6
**定义（目标遗漏集）**
The active target indices not fitted by the proxy.
-/
def target_miss_set
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal) : Set β :=
  active_target_indices target U \ target_fit_set d target proxy U eps

/--
OET anchor: h-5519d2d2e212fbd6
**定义（可达目标拟合集族）**
The family of target-fit sets achieved by candidates in `A`.
-/
def reachable_target_fit_sets
    (target : β → Operator X bot) (A : Set (Operator X bot))
    (U : Set X) (eps : I → ENNReal) : Set (Set β) :=
  {S | ∃ proxy ∈ A, target_fit_set d target proxy U eps = S}

/--
OET anchor: h-5519d2d2e212fbd6
**定义（目标拟合前沿）**
The inclusion-maximal target-fit sets among the candidates.
-/
def target_fit_frontier
    (target : β → Operator X bot) (A : Set (Operator X bot))
    (U : Set X) (eps : I → ENNReal) : Set (Set β) :=
  {S | S ∈ reachable_target_fit_sets d target A U eps ∧
    ¬ ∃ T ∈ reachable_target_fit_sets d target A U eps, S ⊂ T}

/--
OET anchor: h-5519d2d2e212fbd6
**网络候选族的外延算子像**
Network representations enter the operator-candidate layer through the image
of their extensional-operator map. Equal extensional operators are therefore
the same member of this candidate set.
-/
def extensional_operator_candidates {Net : Type}
    (extensional_operator : Net → Operator X bot)
    (network_candidates : Set Net) : Set (Operator X bot) :=
  extensional_operator '' network_candidates

theorem active_target_indices_iff_effective_member
    {target : β → Operator X bot} {U : Set X} {b : β} :
    b ∈ active_target_indices target U ↔
      ∃ x, x ∈ effective_family_domain target U ∧
        b ∈ active_indices target U x := by
  constructor
  · intro hb
    rcases hb with ⟨x, hxU, hxdom⟩
    exact ⟨x, ⟨hxU, b, hxdom⟩, ⟨hxU, hxdom⟩⟩
  · rintro ⟨x, _, hxactive⟩
    exact ⟨x, hxactive.1, hxactive.2⟩

/--
OET anchor: h-e7c195c2a7ca7d34
**命题 #h-e7c195c2a7ca7d34（目标拟合集的基本性质）**
A proxy jointly fits the family exactly when its target-fit set is the full
active target-index set.
-/
theorem joint_fitting_iff_target_fit_set_eq_active
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal)
    (heps : ∀ j : I, eps j ≠ ⊤) :
    JointFitting d target proxy U eps ↔
      target_fit_set d target proxy U eps = active_target_indices target U := by
  constructor
  · intro hfit
    apply Set.Subset.antisymm
    · intro b hb
      exact hb.1
    · intro b hb
      refine ⟨hb, ?_, ?_⟩
      · intro x hx
        exact hfit.proxy_dom ⟨hx.1, b, hx.2⟩
      · intro x hx j
        exact hfit.error x ⟨hx.1, b, hx.2⟩ b ⟨hx.1, hx.2⟩ j
  · intro heq
    refine ⟨heps, ?_, ?_⟩
    · intro x hx
      rcases hx with ⟨hxU, b, hxdom⟩
      have hbfit : b ∈ target_fit_set d target proxy U eps := by
        rw [heq]
        exact ⟨x, hxU, hxdom⟩
      exact hbfit.2.1 ⟨hxU, hxdom⟩
    · intro x hx b hb j
      have hbfit : b ∈ target_fit_set d target proxy U eps := by
        rw [heq]
        exact ⟨x, hb.1, hb.2⟩
      exact hbfit.2.2 x ⟨hb.1, hb.2⟩ j

/--
OET anchor: h-e7c195c2a7ca7d34
**命题 #h-e7c195c2a7ca7d34（候选族中的联合拟合判据）**
Some candidate jointly fits the target family iff the full active target-index
set is reachable as a target-fit set.
-/
theorem candidate_joint_fitting_iff_active_fit_set_reachable
    (target : β → Operator X bot) (A : Set (Operator X bot))
    (U : Set X) (eps : I → ENNReal)
    (heps : ∀ j : I, eps j ≠ ⊤) :
    (∃ proxy ∈ A, JointFitting d target proxy U eps) ↔
      active_target_indices target U ∈
        reachable_target_fit_sets d target A U eps := by
  constructor
  · rintro ⟨proxy, hproxyA, hfit⟩
    exact ⟨proxy, hproxyA,
      (joint_fitting_iff_target_fit_set_eq_active d target proxy U eps heps).mp hfit⟩
  · rintro ⟨proxy, hproxyA, hfitset⟩
    exact ⟨proxy, hproxyA,
      (joint_fitting_iff_target_fit_set_eq_active d target proxy U eps heps).mpr hfitset⟩

/--
OET anchor: h-e7c195c2a7ca7d34
**命题 #h-e7c195c2a7ca7d34（无联合拟合时遗漏非空）**
If the full active target-index set is not reachable and the active set is
nonempty, every candidate misses at least one active target.
-/
theorem target_miss_set_nonempty_of_active_unreachable
    (target : β → Operator X bot) (A : Set (Operator X bot))
    (U : Set X) (eps : I → ENNReal)
    (hunreachable :
      active_target_indices target U ∉
        reachable_target_fit_sets d target A U eps)
    (hactive : (active_target_indices target U).Nonempty) :
    ∀ proxy ∈ A, (target_miss_set d target proxy U eps).Nonempty := by
  have _ := hactive
  intro proxy hproxyA
  by_contra hnone
  have hsubset :
      active_target_indices target U ⊆ target_fit_set d target proxy U eps := by
    intro b hb
    by_contra hbfit
    exact hnone ⟨b, hb, hbfit⟩
  have heq : target_fit_set d target proxy U eps = active_target_indices target U := by
    apply Set.Subset.antisymm
    · intro b hb
      exact hb.1
    · exact hsubset
  exact hunreachable ⟨proxy, hproxyA, heq⟩

/--
OET anchor: h-e7c195c2a7ca7d34
**命题（目标拟合集的基本性质，前沿扩张）**
Every reachable target-fit set is contained in a reachable inclusion-maximal
target-fit set.
-/
theorem reachable_fit_set_subset_frontier
    (target : β → Operator X bot) (A : Set (Operator X bot))
    (U : Set X) (eps : I → ENNReal)
    {S : Set β}
    (hS : S ∈ reachable_target_fit_sets d target A U eps) :
    ∃ T ∈ target_fit_frontier d target A U eps, S ⊆ T := by
  classical
  let candidates : Set (Set β) :=
    {T | T ∈ reachable_target_fit_sets d target A U eps ∧ S ⊆ T}
  have hcandidates_nonempty : candidates.Nonempty := by
    exact ⟨S, hS, Set.Subset.rfl⟩
  have hcandidates_finite : candidates.Finite := Set.toFinite candidates
  rcases hcandidates_finite.exists_maximal hcandidates_nonempty with
    ⟨T, hT, hmax⟩
  refine ⟨T, ?_, hT.2⟩
  refine ⟨hT.1, ?_⟩
  rintro ⟨T', hT'reach, hstrict⟩
  have hT'_candidate : T' ∈ candidates :=
    ⟨hT'reach, Set.Subset.trans hT.2 hstrict.1⟩
  have hreverse : T' ⊆ T := hmax hT'_candidate hstrict.1
  exact hstrict.2 hreverse

/--
OET anchor: h-e7c195c2a7ca7d34
**命题（目标拟合集的基本性质，前沿非空）**
A nonempty candidate family has a nonempty target-fit frontier.
-/
theorem target_fit_frontier_nonempty
    (target : β → Operator X bot) (A : Set (Operator X bot))
    (U : Set X) (eps : I → ENNReal)
    (hA : A.Nonempty) :
    (target_fit_frontier d target A U eps).Nonempty := by
  rcases hA with ⟨proxy, hproxy⟩
  have hreachable :
      target_fit_set d target proxy U eps ∈
        reachable_target_fit_sets d target A U eps :=
    ⟨proxy, hproxy, rfl⟩
  rcases reachable_fit_set_subset_frontier d target A U eps hreachable with
    ⟨T, hT, _⟩
  exact ⟨T, hT⟩

/--
OET anchor: h-e7c195c2a7ca7d34
**命题（目标拟合集的基本性质，前沿反链）**
Two frontier members related by inclusion are equal.
-/
theorem target_fit_frontier_eq_of_subset
    (target : β → Operator X bot) (A : Set (Operator X bot))
    (U : Set X) (eps : I → ENNReal)
    {S T : Set β}
    (hS : S ∈ target_fit_frontier d target A U eps)
    (hT : T ∈ target_fit_frontier d target A U eps)
    (hsub : S ⊆ T) :
    S = T := by
  apply Set.Subset.antisymm hsub
  by_contra hnot
  have hstrict : S ⊂ T := ⟨hsub, hnot⟩
  exact hS.2 ⟨T, hT.1, hstrict⟩

/--
OET anchor: h-904b1a51d72852bd
**命题 #h-904b1a51d72852bd（联合拟合的逐点交会判据）**
The local feasible cell at `x` is the intersection of all active target balls.
-/
def local_joint_feasible_cell
    (target : β → Operator X bot) (U : Set X) (eps : I → ENNReal) (x : X) :
    Set X :=
  { y | ∀ b : β, b ∈ active_indices target U x → ∀ j : I,
      d j ((target b).func x) y ≤ eps j }

/--
OET anchor: h-904b1a51d72852bd
**命题 #h-904b1a51d72852bd（联合拟合的逐点交会判据）**
A joint proxy exists exactly when every effective point admits a non-bottom
choice in its local feasible cell.
-/
theorem joint_fitting_pointwise_intersection_criterion
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (U : Set X) (eps : I → ENNReal)
    (heps : ∀ j : I, eps j ≠ ⊤) :
    (∃ proxy : Operator X bot, JointFitting d target proxy U eps) ↔
      ∃ s : {x // x ∈ effective_family_domain target U} → X,
        ∀ x : {x // x ∈ effective_family_domain target U},
          s x ∈ local_joint_feasible_cell d target U eps x.1 := by
  classical
  constructor
  · rintro ⟨proxy, hfit⟩
    refine ⟨fun x => proxy.func x.1, ?_⟩
    intro x b hb j
    exact hfit.error x.1 x.2 b hb j
  · rintro ⟨s, hs_cell⟩
    have hs_dom : ∀ x : {x // x ∈ effective_family_domain target U}, s x ≠ bot := by
      intro x hsbot
      rcases x.2 with ⟨hxU, b, hbdom⟩
      let j : I := Classical.choice inferInstance
      have hcell := hs_cell x b ⟨hxU, hbdom⟩ j
      have htop : d j ((target b).func x.1) bot = ⊤ :=
        (hd j).isolate_bot ((target b).func x.1) hbdom
      rw [hsbot, htop] at hcell
      exact heps j (top_unique hcell)
    let proxy : Operator X bot :=
      { func := fun x =>
          if hx : x ∈ effective_family_domain target U then s ⟨x, hx⟩ else bot
        preserves_bot := by
          have hbot_not : bot ∉ effective_family_domain target U := by
            intro hbot
            rcases hbot with ⟨_, b, hbdom⟩
            exact hbdom (target b).preserves_bot
          simp [hbot_not] }
    refine ⟨proxy, ?_⟩
    refine ⟨heps, ?_, ?_⟩
    · intro x hx
      dsimp [proxy, dom]
      simpa only [dif_pos hx] using hs_dom ⟨x, hx⟩
    · intro x hx b hb j
      dsimp [proxy]
      simpa only [dif_pos hx] using hs_cell ⟨x, hx⟩ b hb j

/-- Internal local-cell monotonicity helper. -/
theorem local_joint_feasible_cell_extension_mono
    (target_old target_new : β → Operator X bot)
    (U : Set X) (eps : I → ENNReal) (x y : X)
    (hactive :
      ∀ b : β, b ∈ active_indices target_old U x →
        b ∈ active_indices target_new U x)
    (hagrees :
      ∀ b : β, b ∈ active_indices target_old U x →
        (target_new b).func x = (target_old b).func x)
    (hy : y ∈ local_joint_feasible_cell d target_new U eps x) :
    y ∈ local_joint_feasible_cell d target_old U eps x := by
  intro b hb j
  have hnew := hy b (hactive b hb) j
  simpa [hagrees b hb] using hnew

/-- Internal same-index family-extension helper. -/
theorem family_extension_constraint_monotonicity
    (target_old target_new : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal)
    (heff :
      effective_family_domain target_old U ⊆ effective_family_domain target_new U)
    (hactive :
      ∀ x ∈ effective_family_domain target_old U, ∀ b : β,
        b ∈ active_indices target_old U x →
          b ∈ active_indices target_new U x)
    (hagrees :
      ∀ x ∈ effective_family_domain target_old U, ∀ b : β,
        b ∈ active_indices target_old U x →
          (target_new b).func x = (target_old b).func x)
    (hfit : JointFitting d target_new proxy U eps) :
    JointFitting d target_old proxy U eps := by
  refine ⟨hfit.tolerance_finite, ?_, ?_⟩
  · intro x hx
    exact hfit.proxy_dom (heff hx)
  · intro x hx b hb j
    have hnew := hfit.error x (heff hx) b (hactive x hx b hb) j
    simpa [hagrees x hx b hb] using hnew

/--
OET anchor: h-8aba0c37a946e599
**推论（族扩张的约束单调性）**
An indexed-family extension obtained through an index embedding can only add
joint fitting constraints.
-/
theorem indexed_family_extension_constraint_monotonicity
    {β' : Type} [Fintype β'] [Nonempty β']
    (target_old : β → Operator X bot) (target_new : β' → Operator X bot)
    (embed : β → β')
    (hagrees : ∀ b : β, target_new (embed b) = target_old b)
    (proxy : Operator X bot) (U : Set X) (eps : I → ENNReal)
    (hfit : JointFitting d target_new proxy U eps) :
    JointFitting d target_old proxy U eps := by
  refine ⟨hfit.tolerance_finite, ?_, ?_⟩
  · intro x hx
    rcases hx with ⟨hxU, b, hbdom⟩
    apply hfit.proxy_dom
    refine ⟨hxU, embed b, ?_⟩
    simpa [hagrees b] using hbdom
  · intro x hx b hb j
    have hx_new : x ∈ effective_family_domain target_new U := by
      refine ⟨hx.1, embed b, ?_⟩
      simpa [hagrees b] using hb.2
    have hb_new : embed b ∈ active_indices target_new U x := by
      refine ⟨hb.1, ?_⟩
      simpa [hagrees b] using hb.2
    simpa [hagrees b] using hfit.error x hx_new (embed b) hb_new j

/--
OET anchor: h-8aba0c37a946e599
**推论（族扩张的约束单调性，逐点可行胞）**
At every old effective point, the feasible cell of an indexed-family extension
is contained in the old feasible cell.
-/
theorem indexed_family_extension_feasible_cell_subset
    {β' : Type} [Fintype β'] [Nonempty β']
    (target_old : β → Operator X bot) (target_new : β' → Operator X bot)
    (embed : β → β')
    (hagrees : ∀ b : β, target_new (embed b) = target_old b)
    (U : Set X) (eps : I → ENNReal) {x y : X}
    (hx : x ∈ effective_family_domain target_old U)
    (hy : y ∈ local_joint_feasible_cell d target_new U eps x) :
    y ∈ local_joint_feasible_cell d target_old U eps x := by
  have _ := hx
  intro b hb j
  have hb_new : embed b ∈ active_indices target_new U x := by
    refine ⟨hb.1, ?_⟩
    simpa [hagrees b] using hb.2
  simpa [hagrees b] using hy (embed b) hb_new j

/--
OET anchor: h-d19df30020574dc4
**推论 #h-d19df30020574dc4（值恒等子族的分歧退化）**
If two target members agree pointwise on their overlap, their domain-level
pairwise divergence is zero.
-/
theorem value_identical_subfamily_domain_divergence_zero
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (U : Set X) (A' : Set β)
    (hident :
      ∀ a ∈ A', ∀ b ∈ A', a ≠ b →
        ∀ x ∈ overlap_domain target U a b,
          (target a).func x = (target b).func x) :
    ∀ a ∈ A', ∀ b ∈ A', a ≠ b → ∀ j : I,
      domain_divergence d target U a b j = 0 := by
  intro a ha b hb hne j
  apply le_antisymm
  · unfold domain_divergence
    apply iSup_le
    intro x
    simp [pairwise_divergence, hident a ha b hb hne x.1 x.2, (hd j).dist_self]
  · exact zero_le _

/--
OET anchor: h-d19df30020574dc4
**推论（值恒等子族的分歧退化，像距恒等）**
Pointwise-identical targets have identical within-target pairwise image
distances on every pairwise overlap.
-/
theorem value_identical_subfamily_pair_distance_eq
    (target : β → Operator X bot) (U : Set X) (A' : Set β)
    (hident :
      ∀ a ∈ A', ∀ b ∈ A', a ≠ b →
        ∀ x ∈ overlap_domain target U a b,
          (target a).func x = (target b).func x) :
    ∀ a ∈ A', ∀ b ∈ A', a ≠ b →
      ∀ x ∈ overlap_domain target U a b,
      ∀ y ∈ overlap_domain target U a b,
      ∀ j : I,
        d j ((target a).func x) ((target a).func y) =
          d j ((target b).func x) ((target b).func y) := by
  intro a ha b hb hab x hx y hy j
  rw [hident a ha b hb hab x hx, hident a ha b hb hab y hy]

/--
OET anchor: h-d19df30020574dc4
**推论（值恒等子族的分歧退化，共同域归约）**
On a common effective domain, repeating pointwise-identical target constraints
does not change the fitting class.
-/
theorem value_identical_subfamily_fitting_iff_single_target
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U D : Set X) (A' : Set β) (a₀ : β) (ha₀ : a₀ ∈ A')
    (eps : I → ENNReal)
    (hdom : ∀ a ∈ A', U ∩ dom (target a) = D)
    (hident : ∀ a ∈ A', ∀ x ∈ D,
      (target a).func x = (target a₀).func x) :
    (∀ a ∈ A', InFullFittingBall d (target a) proxy D eps) ↔
      InFullFittingBall d (target a₀) proxy D eps := by
  constructor
  · intro hall
    exact hall a₀ ha₀
  · intro hsingle a ha
    refine ⟨hsingle.tolerance_finite, ?_, hsingle.proxy_dom, ?_⟩
    · intro x hxD
      have hx : x ∈ U ∩ dom (target a) := by
        simpa [hdom a ha] using hxD
      exact hx.2
    · intro x hx j _
      rw [hident a ha x hx]
      exact hsingle.error x hx j (Set.mem_univ j)

lemma active_of_overlap_left
    {target : β → Operator X bot} {U : Set X} {a b : β} {x : X}
    (hx : x ∈ overlap_domain target U a b) :
    a ∈ active_indices target U x := by
  rcases hx with ⟨⟨heff, ha⟩, _⟩
  exact ⟨heff.1, ha⟩

lemma active_of_overlap_right
    {target : β → Operator X bot} {U : Set X} {a b : β} {x : X}
    (hx : x ∈ overlap_domain target U a b) :
    b ∈ active_indices target U x := by
  rcases hx with ⟨⟨heff, _⟩, hb⟩
  exact ⟨heff.1, hb⟩

/--
OET anchor: h-487e97ae10758368
**命题 #h-487e97ae10758368（分歧不可拟合判据）**
If two active targets at one point are farther apart than the two fitting
tolerances, no joint fitting proxy can satisfy the stated tolerance.
-/
theorem divergence_unfittable
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal)
    {a b : β} {x : X} {j : I}
    (hab : a ≠ b)
    (hx : x ∈ overlap_domain target U a b)
    (hdiv :
      pairwise_divergence d target a b x j > eps j + eps j) :
    ¬ JointFitting d target proxy U eps := by
  have _ := hab
  intro hfit
  have ha := active_of_overlap_left (target := target) (U := U) (a := a) (b := b) hx
  have hb := active_of_overlap_right (target := target) (U := U) (a := a) (b := b) hx
  have heff : x ∈ effective_family_domain target U := hx.1.1
  have hα : d j ((target a).func x) (proxy.func x) ≤ eps j :=
    hfit.error x heff a ha j
  have hβ_raw : d j ((target b).func x) (proxy.func x) ≤ eps j :=
    hfit.error x heff b hb j
  have hβ : d j (proxy.func x) ((target b).func x) ≤ eps j := by
    simpa [(hd j).symm (proxy.func x) ((target b).func x)] using hβ_raw
  have htri :=
    (hd j).triangle ((target a).func x) (proxy.func x) ((target b).func x)
  have hle :
      pairwise_divergence d target a b x j ≤ eps j + eps j := by
    exact le_trans htri (add_le_add hα hβ)
  exact not_lt_of_ge hle hdiv

/--
OET anchor: h-b35b299b59262950
**命题（异容限成对相容界）**
Two targets approximated by the same point with possibly different finite
tolerances are separated by at most the sum of those tolerances.
-/
theorem heterogeneous_tolerance_pair_compatibility
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target_a target_b : Operator X bot)
    (x y : X) (j : I) (eta delta : ENNReal)
    (heta : eta ≠ ⊤) (hdelta : delta ≠ ⊤)
    (ha : d j (target_a.func x) y ≤ eta)
    (hb : d j (target_b.func x) y ≤ delta) :
    d j (target_a.func x) (target_b.func x) ≤ eta + delta := by
  have _ := heta
  have _ := hdelta
  have hb_symm : d j y (target_b.func x) ≤ delta := by
    simpa [(hd j).symm y (target_b.func x)] using hb
  exact le_trans
    ((hd j).triangle (target_a.func x) y (target_b.func x))
    (add_le_add ha hb_symm)

/--
OET anchor: h-b35b299b59262950
**命题（异容限成对相容界，反向障碍）**
Strict separation beyond the tolerance sum excludes a common approximating
point.
-/
theorem no_common_approximation_of_pair_separation
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target_a target_b : Operator X bot)
    (x y : X) (j : I) (eta delta : ENNReal)
    (heta : eta ≠ ⊤) (hdelta : delta ≠ ⊤)
    (hsep : eta + delta < d j (target_a.func x) (target_b.func x)) :
    ¬(d j (target_a.func x) y ≤ eta ∧
      d j (target_b.func x) y ≤ delta) := by
  rintro ⟨ha, hb⟩
  exact not_lt_of_ge
    (heterogeneous_tolerance_pair_compatibility d hd target_a target_b x y j
      eta delta heta hdelta ha hb) hsep

/--
OET anchor: h-3d057004dafe2e46
**推论 #h-3d057004dafe2e46（域级分歧不可拟合）**
The pointwise criterion follows from a strict domain-level supremum bound.
-/
theorem domain_divergence_unfittable
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal)
    {a b : β} {j : I}
    (hab : a ≠ b)
    (hdiv : domain_divergence d target U a b j > eps j + eps j) :
    ¬ JointFitting d target proxy U eps := by
  have h_exists := (lt_iSup_iff.mp hdiv)
  rcases h_exists with ⟨x, hx_gt⟩
  exact divergence_unfittable d hd target proxy U eps hab x.2 hx_gt

/--
OET anchor: h-68e510dbbcca4760
**推论 #h-68e510dbbcca4760（族分歧半径的必要容限界）**
Any joint fitting certificate forces every pairwise target divergence on an
overlap to be bounded by the sum of the two fitting tolerances.
-/
theorem domain_divergence_le_two_eps_of_joint_fitting
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal)
    (hfit : JointFitting d target proxy U eps) :
    ∀ a b : β, ∀ j : I,
      domain_divergence d target U a b j ≤ eps j + eps j := by
  intro a b j
  unfold domain_divergence
  apply iSup_le
  intro x
  have hx := x.2
  have ha := active_of_overlap_left (target := target) (U := U) (a := a) (b := b) hx
  have hb := active_of_overlap_right (target := target) (U := U) (a := a) (b := b) hx
  have heff : x.1 ∈ effective_family_domain target U := hx.1.1
  have hα : d j ((target a).func x.1) (proxy.func x.1) ≤ eps j :=
    hfit.error x.1 heff a ha j
  have hβ_raw : d j ((target b).func x.1) (proxy.func x.1) ≤ eps j :=
    hfit.error x.1 heff b hb j
  have hβ : d j (proxy.func x.1) ((target b).func x.1) ≤ eps j := by
    simpa [(hd j).symm (proxy.func x.1) ((target b).func x.1)] using hβ_raw
  have htri :=
    (hd j).triangle ((target a).func x.1) (proxy.func x.1) ((target b).func x.1)
  exact le_trans htri (add_le_add hα hβ)

/--
OET anchor: h-68e510dbbcca4760
**推论 #h-68e510dbbcca4760（族分歧半径的必要容限界，族上确界形式）**
The supremal pairwise divergence of the target family is bounded by twice the
component tolerance whenever a joint fitting proxy exists.
-/
theorem family_pairwise_divergence_supremum_le_two_eps_of_joint_fitting
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal)
    (hfit : JointFitting d target proxy U eps) :
    ∀ j : I, family_pairwise_divergence_supremum d target U j ≤ eps j + eps j := by
  intro j
  unfold family_pairwise_divergence_supremum
  apply iSup_le
  intro p
  exact domain_divergence_le_two_eps_of_joint_fitting d hd target proxy U eps
    hfit p.1.1 p.1.2 j

/--
OET anchor: h-68e510dbbcca4760
**推论（族成对分歧的必要容限界）**
Joint fitting forces every component tolerance to dominate half of the
supremal pairwise divergence.
-/
theorem pairwise_tolerance_lower_bound_le_of_joint_fitting
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal)
    (hfit : JointFitting d target proxy U eps) :
    ∀ j : I, pairwise_tolerance_lower_bound d target U j ≤ eps j := by
  intro j
  apply (ENNReal.div_le_iff (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤)).2
  simpa [mul_two] using
    family_pairwise_divergence_supremum_le_two_eps_of_joint_fitting d hd target proxy U eps hfit j

/--
OET anchor: h-68e510dbbcca4760
**推论（族成对分歧的必要容限界，零值刻画）**
The pairwise lower bound vanishes exactly when every distinct active target
pair has zero distance on its overlap domain.
-/
theorem pairwise_tolerance_lower_bound_eq_zero_iff
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (U : Set X) (j : I) :
    pairwise_tolerance_lower_bound d target U j = 0 ↔
      ∀ a b : β, a ≠ b → ∀ x ∈ overlap_domain target U a b,
        d j ((target a).func x) ((target b).func x) = 0 := by
  have _ := hd
  constructor
  · intro hlower a b hab x hx
    have hcost_zero : family_pairwise_divergence_supremum d target U j = 0 := by
      simpa [pairwise_tolerance_lower_bound] using hlower
    have hdomain : domain_divergence d target U a b j ≤
        family_pairwise_divergence_supremum d target U j := by
      unfold family_pairwise_divergence_supremum
      exact le_iSup
        (fun p : {p : β × β // p.1 ≠ p.2} =>
          domain_divergence d target U p.1.1 p.1.2 j)
        ⟨(a, b), hab⟩
    have hpoint : d j ((target a).func x) ((target b).func x) ≤
        domain_divergence d target U a b j := by
      simpa [domain_divergence, pairwise_divergence] using
        (le_iSup
          (fun y : {z // z ∈ overlap_domain target U a b} =>
            pairwise_divergence d target a b y.1 j)
          ⟨x, hx⟩)
    exact le_antisymm (by simpa [hcost_zero] using le_trans hpoint hdomain) (zero_le _)
  · intro hzero
    unfold pairwise_tolerance_lower_bound
    have hcost_zero : family_pairwise_divergence_supremum d target U j = 0 := by
      apply le_antisymm
      · unfold family_pairwise_divergence_supremum
        apply iSup_le
        intro p
        unfold domain_divergence
        apply iSup_le
        intro x
        simp [pairwise_divergence, hzero p.1.1 p.1.2 p.2 x.1 x.2]
      · exact zero_le _
    simp [hcost_zero]

/--
OET anchor: h-f7f8c2ed3a2a3a3e
**定义（δ-近族）**
All distinct target pairs have componentwise domain divergence at most `δ`.
-/
def DeltaNearFamily
    (target : β → Operator X bot) (U : Set X) (delta : ENNReal) : Prop :=
  ∀ a b : β, a ≠ b → ∀ j : I,
    domain_divergence d target U a b j ≤ delta

/-- A delta-near family has supremal pairwise divergence at most `delta`. -/
theorem family_pairwise_divergence_supremum_le_of_delta_near
    (target : β → Operator X bot) (U : Set X) (delta : ENNReal)
    (hnear : DeltaNearFamily d target U delta) :
    ∀ j : I, family_pairwise_divergence_supremum d target U j ≤ delta := by
  intro j
  unfold family_pairwise_divergence_supremum
  apply iSup_le
  intro p
  exact hnear p.1.1 p.1.2 p.2 j

lemma pairwise_divergence_le_domain_divergence
    (target : β → Operator X bot) (U : Set X)
    {a b : β} {x : X} (hx : x ∈ overlap_domain target U a b) (j : I) :
    pairwise_divergence d target a b x j ≤
      domain_divergence d target U a b j := by
  unfold domain_divergence
  exact le_iSup
    (fun y : {z // z ∈ overlap_domain target U a b} =>
      pairwise_divergence d target a b y.1 j)
    ⟨x, hx⟩

/--
OET anchor: h-f7f8c2ed3a2a3a3e
**命题（delta-近族的成对界，必要容限）**
The pairwise tolerance lower bound of a delta-near family is at most
`delta / 2`.
-/
theorem pairwise_tolerance_lower_bound_le_half_of_delta_near
    (target : β → Operator X bot) (U : Set X) (delta : ENNReal)
    (hnear : DeltaNearFamily d target U delta) :
    ∀ j : I, pairwise_tolerance_lower_bound d target U j ≤ delta / 2 := by
  intro j
  exact ENNReal.div_le_div_right
    (family_pairwise_divergence_supremum_le_of_delta_near d target U delta hnear j) 2

/--
OET anchor: h-f7f8c2ed3a2a3a3e
**命题（delta-近族的成对界，像距扰动）**
On every pairwise overlap, the two target image distances differ by at most
two endpoint delta-errors in the order-theoretic sense.
-/
theorem delta_near_pair_image_distance_bounds
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (U : Set X) (delta : ENNReal)
    (hnear : DeltaNearFamily d target U delta)
    {a b : β} (hab : a ≠ b) {x y : X}
    (hx : x ∈ overlap_domain target U a b)
    (hy : y ∈ overlap_domain target U a b) (j : I) :
    d j ((target a).func x) ((target a).func y) ≤
        d j ((target b).func x) ((target b).func y) + (delta + delta) ∧
      d j ((target b).func x) ((target b).func y) ≤
        d j ((target a).func x) ((target a).func y) + (delta + delta) := by
  have hax_bx : d j ((target a).func x) ((target b).func x) ≤ delta :=
    le_trans (pairwise_divergence_le_domain_divergence d target U hx j)
      (hnear a b hab j)
  have hay_by : d j ((target a).func y) ((target b).func y) ≤ delta :=
    le_trans (pairwise_divergence_le_domain_divergence d target U hy j)
      (hnear a b hab j)
  have hbx_ax : d j ((target b).func x) ((target a).func x) ≤ delta := by
    simpa [(hd j).symm ((target b).func x) ((target a).func x)] using hax_bx
  have hby_ay : d j ((target b).func y) ((target a).func y) ≤ delta := by
    simpa [(hd j).symm ((target b).func y) ((target a).func y)] using hay_by
  constructor
  · have htri₁ := (hd j).triangle ((target a).func x) ((target b).func x)
      ((target a).func y)
    have htri₂ := (hd j).triangle ((target b).func x) ((target b).func y)
      ((target a).func y)
    calc
      d j ((target a).func x) ((target a).func y)
          ≤ d j ((target a).func x) ((target b).func x) +
            d j ((target b).func x) ((target a).func y) := htri₁
      _ ≤ delta +
            (d j ((target b).func x) ((target b).func y) + delta) :=
          add_le_add hax_bx (le_trans htri₂ (add_le_add le_rfl hby_ay))
      _ = d j ((target b).func x) ((target b).func y) + (delta + delta) := by
          simp [add_comm, add_assoc]
  · have htri₁ := (hd j).triangle ((target b).func x) ((target a).func x)
      ((target b).func y)
    have htri₂ := (hd j).triangle ((target a).func x) ((target a).func y)
      ((target b).func y)
    calc
      d j ((target b).func x) ((target b).func y)
          ≤ d j ((target b).func x) ((target a).func x) +
            d j ((target a).func x) ((target b).func y) := htri₁
      _ ≤ delta +
            (d j ((target a).func x) ((target a).func y) + delta) :=
          add_le_add hbx_ax (le_trans htri₂ (add_le_add le_rfl hay_by))
      _ = d j ((target a).func x) ((target a).func y) + (delta + delta) := by
          simp [add_comm, add_assoc]

/--
OET anchor: h-f7f8c2ed3a2a3a3e
**命题（delta-近族的成对界，有限像距差）**
When both image distances and delta are finite, their real-valued absolute
difference is at most twice delta.
-/
theorem delta_near_pair_image_distance_to_real_abs_le
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (U : Set X) (delta : ENNReal)
    (hnear : DeltaNearFamily d target U delta)
    {a b : β} (hab : a ≠ b) {x y : X}
    (hx : x ∈ overlap_domain target U a b)
    (hy : y ∈ overlap_domain target U a b) (j : I)
    (ha_finite : d j ((target a).func x) ((target a).func y) ≠ ⊤)
    (hb_finite : d j ((target b).func x) ((target b).func y) ≠ ⊤)
    (hdelta_finite : delta ≠ ⊤) :
    |(d j ((target a).func x) ((target a).func y)).toReal -
        (d j ((target b).func x) ((target b).func y)).toReal| ≤
      2 * delta.toReal := by
  rcases delta_near_pair_image_distance_bounds d hd target U delta hnear hab hx hy j with
    ⟨hab_bound, hba_bound⟩
  have htwo_finite : delta + delta ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hdelta_finite, hdelta_finite⟩
  have hab_real :
      (d j ((target a).func x) ((target a).func y)).toReal ≤
        (d j ((target b).func x) ((target b).func y)).toReal +
          2 * delta.toReal := by
    have hsum_finite :
        d j ((target b).func x) ((target b).func y) + (delta + delta) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨hb_finite, htwo_finite⟩
    have := (ENNReal.toReal_le_toReal ha_finite hsum_finite).2 hab_bound
    simpa [ENNReal.toReal_add, hb_finite, hdelta_finite, two_mul] using this
  have hba_real :
      (d j ((target b).func x) ((target b).func y)).toReal ≤
        (d j ((target a).func x) ((target a).func y)).toReal +
          2 * delta.toReal := by
    have hsum_finite :
        d j ((target a).func x) ((target a).func y) + (delta + delta) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨ha_finite, htwo_finite⟩
    have := (ENNReal.toReal_le_toReal hb_finite hsum_finite).2 hba_bound
    simpa [ENNReal.toReal_add, ha_finite, hdelta_finite, two_mul] using this
  rw [abs_le]
  constructor <;> linarith

/--
OET anchor: h-e158434843cf7652
**定义（选择归约算子）**
The target operator selected pointwise by an admissible choice map.
-/
noncomputable def selection_reduced_operator
    (target : β → Operator X bot) (U : Set X) (sigma : X → β) :
    Operator X bot :=
  by
    classical
    exact
      { func := fun x =>
          if hx : x ∈ effective_family_domain target U then
            (target (sigma x)).func x
          else
            bot
        preserves_bot := by
          by_cases hbot : bot ∈ effective_family_domain target U
          · simp [hbot, (target (sigma bot)).preserves_bot]
          · simp [hbot] }

lemma selection_reduced_operator_eq_of_mem
    (target : β → Operator X bot) (U : Set X) (sigma : X → β)
    {x : X} (hx : x ∈ effective_family_domain target U) :
    (selection_reduced_operator target U sigma).func x = (target (sigma x)).func x := by
  classical
  simp [selection_reduced_operator, hx]

lemma selection_reduced_operator_dom
    (target : β → Operator X bot) (U : Set X) (sigma : X → β)
    (hsigma :
      ∀ x ∈ effective_family_domain target U,
        sigma x ∈ active_indices target U x) :
    effective_family_domain target U ⊆ dom (selection_reduced_operator target U sigma) := by
  intro x hx
  have hs := hsigma x hx
  have hdom : x ∈ dom (target (sigma x)) := hs.2
  simpa [dom, selection_reduced_operator_eq_of_mem target U sigma hx] using hdom

/--
OET anchor: h-a9984fd2a088982a
**命题（选择归约拟合的反向偏差界，选择偏差）**
The worst distance from the selected target value to any active target value
at the same effective input.
-/
noncomputable def selection_divergence
    (target : β → Operator X bot) (U : Set X) (sigma : X → β) (j : I) :
    ENNReal :=
  ⨆ x : {x // x ∈ effective_family_domain target U},
    ⨆ b : {b // b ∈ active_indices target U x.1},
      d j ((target b.1).func x.1) ((target (sigma x.1)).func x.1)

lemma active_pair_divergence_le_selection_divergence
    (target : β → Operator X bot) (U : Set X) (sigma : X → β)
    {x : X} (hx : x ∈ effective_family_domain target U)
    {b : β} (hb : b ∈ active_indices target U x) (j : I) :
    d j ((target b).func x) ((target (sigma x)).func x) ≤
      selection_divergence d target U sigma j := by
  unfold selection_divergence
  exact le_trans
    (le_iSup (fun c : {c // c ∈ active_indices target U x} =>
      d j ((target c.1).func x) ((target (sigma x)).func x)) ⟨b, hb⟩)
    (le_iSup (fun z : {z // z ∈ effective_family_domain target U} =>
      ⨆ c : {c // c ∈ active_indices target U z.1},
        d j ((target c.1).func z.1) ((target (sigma z.1)).func z.1)) ⟨x, hx⟩)

/-- The selection-dependent divergence is bounded by the family-wide supremum. -/
theorem selection_divergence_le_family_pairwise_divergence_supremum
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (U : Set X) (sigma : X → β)
    (hsigma :
      ∀ x ∈ effective_family_domain target U,
        sigma x ∈ active_indices target U x) (j : I) :
    selection_divergence d target U sigma j ≤
      family_pairwise_divergence_supremum d target U j := by
  unfold selection_divergence
  apply iSup_le
  intro x
  apply iSup_le
  intro b
  by_cases hsame : b.1 = sigma x.1
  · rw [hsame, (hd j).dist_self]
    exact zero_le _
  · have hoverlap : x.1 ∈ overlap_domain target U b.1 (sigma x.1) :=
      ⟨⟨x.2, b.2.2⟩, (hsigma x.1 x.2).2⟩
    have hdomain :
        d j ((target b.1).func x.1) ((target (sigma x.1)).func x.1) ≤
          domain_divergence d target U b.1 (sigma x.1) j := by
      simpa [domain_divergence, pairwise_divergence] using
        (le_iSup
          (fun y : {z // z ∈ overlap_domain target U b.1 (sigma x.1)} =>
            pairwise_divergence d target b.1 (sigma x.1) y.1 j)
          ⟨x.1, hoverlap⟩)
    exact le_trans hdomain
      (le_iSup
        (fun p : {p : β × β // p.1 ≠ p.2} =>
          domain_divergence d target U p.1.1 p.1.2 j)
        ⟨(b.1, sigma x.1), hsame⟩)

/--
OET anchor: h-b70a7ff2afc725d2
**引理（联合拟合蕴含选择归约拟合）**
Any joint fitting proxy fits every selection reduction with the same tolerance.
-/
theorem joint_fitting_to_selection_reduced_fitting
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal) (sigma : X → β)
    (hsigma :
      ∀ x ∈ effective_family_domain target U,
        sigma x ∈ active_indices target U x)
    (hfit : JointFitting d target proxy U eps) :
    InFullFittingBall d (selection_reduced_operator target U sigma) proxy
      (effective_family_domain target U) eps := by
  refine ⟨fun j _ => hfit.tolerance_finite j,
    selection_reduced_operator_dom target U sigma hsigma, hfit.proxy_dom, ?_⟩
  intro x hx j _
  rw [selection_reduced_operator_eq_of_mem target U sigma hx]
  exact hfit.error x hx (sigma x) (hsigma x hx) j

/--
OET anchor: h-a9984fd2a088982a
**命题（选择归约拟合的反向偏差界，点态界）**
Selection-reduced fitting gives the joint pointwise bound after adding the
selection-dependent divergence.
-/
theorem selection_reduced_fitting_to_joint_pointwise_bound
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal) (sigma : X → β)
    (hfit :
      InFullFittingBall d (selection_reduced_operator target U sigma) proxy
        (effective_family_domain target U) eps) :
    ∀ x ∈ effective_family_domain target U, ∀ b : β,
      b ∈ active_indices target U x → ∀ j : I,
        d j ((target b).func x) (proxy.func x) ≤
          eps j + selection_divergence d target U sigma j := by
  intro x hx b hb j
  have hmerge :
      (selection_reduced_operator target U sigma).func x = (target (sigma x)).func x :=
    selection_reduced_operator_eq_of_mem target U sigma hx
  have hfit_x :
      d j ((target (sigma x)).func x) (proxy.func x) ≤ eps j := by
    simpa [hmerge] using hfit.error x hx j (Set.mem_univ j)
  have hpair :=
    active_pair_divergence_le_selection_divergence
      d target U sigma hx hb j
  calc
    d j ((target b).func x) (proxy.func x)
        ≤ d j ((target b).func x) ((target (sigma x)).func x) +
          d j ((target (sigma x)).func x) (proxy.func x) :=
      (hd j).triangle _ _ _
    _ ≤ selection_divergence d target U sigma j + eps j :=
      add_le_add hpair hfit_x
    _ = eps j + selection_divergence d target U sigma j := by rw [add_comm]

/--
OET anchor: h-a9984fd2a088982a
**命题（选择归约拟合的反向偏差界）**
A finite selection-dependent divergence gives a genuine joint fitting
tolerance vector.
-/
theorem selection_reduced_fitting_to_joint_fitting
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal) (sigma : X → β)
    (hsigma :
      ∀ x ∈ effective_family_domain target U,
        sigma x ∈ active_indices target U x)
    (heps : ∀ j : I, eps j ≠ ⊤)
    (hdivergence : ∀ j : I, selection_divergence d target U sigma j ≠ ⊤)
    (hfit :
      InFullFittingBall d (selection_reduced_operator target U sigma) proxy
        (effective_family_domain target U) eps) :
    JointFitting d target proxy U
      (fun j => eps j + selection_divergence d target U sigma j) := by
  let hfit' :
      InFullFittingBall d (selection_reduced_operator target U sigma) proxy
        (effective_family_domain target U) eps :=
    { hfit with
      target_dom := selection_reduced_operator_dom target U sigma hsigma }
  refine ⟨?_, hfit.proxy_dom, ?_⟩
  · intro j
    exact ENNReal.add_ne_top.mpr ⟨heps j, hdivergence j⟩
  · exact selection_reduced_fitting_to_joint_pointwise_bound
      d hd target proxy U eps sigma hfit'

/--
OET anchor: h-a9984fd2a088982a
**命题（选择归约拟合的反向偏差界，delta-近族）**
For a delta-near family with `delta ≠ ⊤`, selection-reduced fitting within
`eps` gives joint fitting within the finite tolerance `eps + delta`.
-/
theorem selection_reduced_fitting_to_joint_fitting_of_delta_near
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (target : β → Operator X bot) (proxy : Operator X bot)
    (U : Set X) (eps : I → ENNReal) (delta : ENNReal)
    (sigma : X → β)
    (hsigma :
      ∀ x ∈ effective_family_domain target U,
        sigma x ∈ active_indices target U x)
    (heps : ∀ j : I, eps j ≠ ⊤)
    (hdelta : delta ≠ ⊤)
    (hnear : DeltaNearFamily d target U delta)
    (hfit :
      InFullFittingBall d (selection_reduced_operator target U sigma) proxy
        (effective_family_domain target U) eps) :
    JointFitting d target proxy U (fun j => eps j + delta) := by
  refine ⟨fun j => ENNReal.add_ne_top.mpr ⟨heps j, hdelta⟩, hfit.proxy_dom, ?_⟩
  intro x hx b hb j
  have hpoint :=
    selection_reduced_fitting_to_joint_pointwise_bound
      d hd target proxy U eps sigma hfit x hx b hb j
  exact le_trans hpoint
    (add_le_add le_rfl
      (le_trans
        (selection_divergence_le_family_pairwise_divergence_supremum
          d hd target U sigma hsigma j)
        (family_pairwise_divergence_supremum_le_of_delta_near d target U delta hnear j)))

/-- Internal co-Lip separation helper for downstream composition results. -/
theorem colip_amplified_divergence_unfittable
    [Fintype I]
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (omega target_a target_b proxy : Operator X bot)
    (V : Set X) (K : I → I → ENNReal) (eps : I → ENNReal)
    (hK : IsCoLipMatrix d omega V K)
    {x : X} {j : I}
    (haV : target_a.func x ∈ V)
    (hbV : target_b.func x ∈ V)
    (hpV : proxy.func x ∈ V)
    (hfit_a :
      d j (omega.func (target_a.func x)) (omega.func (proxy.func x)) ≤ eps j)
    (hfit_b :
      d j (omega.func (target_b.func x)) (omega.func (proxy.func x)) ≤ eps j)
    (hamp :
      (∑ i : I, K i j * d i (target_a.func x) (target_b.func x)) >
        eps j + eps j) :
    False := by
  have _ := hpV
  have htri :=
    (hd j).triangle (omega.func (target_a.func x)) (omega.func (proxy.func x))
      (omega.func (target_b.func x))
  have hfit_b_symm :
      d j (omega.func (proxy.func x)) (omega.func (target_b.func x)) ≤ eps j := by
    simpa [(hd j).symm (omega.func (proxy.func x)) (omega.func (target_b.func x))]
      using hfit_b
  have hupper :
      d j (omega.func (target_a.func x)) (omega.func (target_b.func x)) ≤
        eps j + eps j :=
    le_trans htri (add_le_add hfit_a hfit_b_symm)
  have hlower :
      (∑ i : I, K i j * d i (target_a.func x) (target_b.func x)) ≤
        d j (omega.func (target_a.func x)) (omega.func (target_b.func x)) :=
    hK.2.2 (target_a.func x) haV (target_b.func x) hbV j
  exact not_lt_of_ge (le_trans hlower hupper) hamp

/-- Internal zero-fiber helper for downstream composition results. -/
theorem zeroized_pair_same_fiber_dichotomy
    (hd : ∀ j : I, ExtendedPseudoMetric X bot (d j))
    (omega : Operator X bot) {ya yb y : X} {j : I}
    (hzero : d j (omega.func ya) (omega.func yb) = 0) :
    (d j (omega.func ya) (omega.func y) = 0 ∧
      d j (omega.func yb) (omega.func y) = 0) ∨
    (0 < d j (omega.func ya) (omega.func y) ∨
      0 < d j (omega.func yb) (omega.func y)) := by
  by_cases ha : d j (omega.func ya) (omega.func y) = 0
  · left
    refine ⟨ha, ?_⟩
    have htri :=
      (hd j).triangle (omega.func yb) (omega.func ya) (omega.func y)
    have hsymm_zero : d j (omega.func yb) (omega.func ya) = 0 := by
      simpa [(hd j).symm (omega.func yb) (omega.func ya)] using hzero
    have hle : d j (omega.func yb) (omega.func y) ≤ 0 := by
      simpa [hsymm_zero, ha] using htri
    exact le_antisymm hle (zero_le _)
  · right
    left
    exact pos_iff_ne_zero.mpr ha

end

end formal_oet.vol_02.ch_09_family_fitting
