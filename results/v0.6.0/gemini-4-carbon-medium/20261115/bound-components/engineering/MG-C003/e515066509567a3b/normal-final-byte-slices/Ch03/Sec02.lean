import Ch03.Sec01
import Mathlib.Data.Setoid.Partition
 
namespace Ch03
 
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
 
/-! ### 命题 3.5：计算纤维的基本性质 (CH03-P06-01 .. 08) -/
 
theorem subfamily_pseudometric_eq_zero_iff {X I : Type}
    (d : I → X → X → ENNReal) (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  unfold subfamily_pseudometric
  constructor
  · intro h j hj
    have hle : d j x y ≤ ⨆ k : {k // k ∈ J}, d k.1 x y :=
      le_iSup (fun k : {k // k ∈ J} => d k.1 x y) ⟨j, hj⟩
    rw [h] at hle
    exact le_antisymm hle (zero_le _)
  · intro hall
    apply le_antisymm _ (zero_le _)
    apply iSup_le
    intro k
    exact le_of_eq (hall k.1 k.2)
 
/-- CH03-P06-01: 命题 3.5(i) 目标零距不变性（任意目标 `y, y' ∈ 𝒳`）。 -/
theorem prop_3_5_i_target_zero_invariant {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (J : Set I) (y y' : X)
    (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty)
    (hyy' : subfamily_pseudometric d J y y' = 0) :
    CompFiber d ϕ J y U = CompFiber d ϕ J y' U := by
  have hy_all := (subfamily_pseudometric_eq_zero_iff d J y y').mp hyy'
  ext x
  simp only [CompFiber, Set.mem_setOf_eq, subfamily_pseudometric_eq_zero_iff]
  refine and_congr_right fun _ => ⟨fun hx j hj => ?_, fun hx j hj => ?_⟩
  · apply le_antisymm _ (zero_le _)
    calc
      d j (ϕ.func x) y' ≤ d j (ϕ.func x) y + d j y y' := (hd j).triangle _ _ _
      _ = 0 := by rw [hx j hj, hy_all j hj, zero_add]
  · apply le_antisymm _ (zero_le _)
    calc
      d j (ϕ.func x) y ≤ d j (ϕ.func x) y' + d j y' y := (hd j).triangle _ _ _
      _ = 0 := by rw [hx j hj, (hd j).symm y' y, hy_all j hj, zero_add]
 
/-- CH03-P06-02: 命题 3.5(ii-a) 像目标纤维非空且覆盖 `U`。 -/
theorem prop_3_5_ii_a_nonempty_and_cover {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (J : Set I)
    (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty) :
    (∀ y ∈ operator_image ϕ U, (CompFiber d ϕ J y U).Nonempty) ∧
    (⋃ y ∈ operator_image ϕ U, CompFiber d ϕ J y U) = U := by
  have hself : ∀ z : X, subfamily_pseudometric d J z z = 0 := fun z =>
    (subfamily_pseudometric_eq_zero_iff d J z z).mpr (fun j _ => (hd j).dist_self z)
  refine ⟨?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, hself (ϕ.func x)⟩
  · ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨_, _, hx⟩
      exact hx.1
    · intro hx
      exact ⟨ϕ.func x, ⟨x, hx, rfl⟩, hx, hself (ϕ.func x)⟩
 
/-- 去重后的计算纤维集合族 `{Fib_{ϕ, J}(y | U) : y ∈ ϕ(U)}`。 -/
def CompFiberPartition {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (U : Set X) : Set (Set X) :=
  {F : Set X | ∃ y ∈ operator_image ϕ U, F = CompFiber d ϕ J y U}
 
/-- 在子类型 `↥U` 上去重后的计算纤维集合族。 -/
def CompFiberSubtypePartition {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (U : Set X) : Set (Set ↥U) :=
  {F : Set ↥U | ∃ y ∈ operator_image ϕ U, F = {x : ↥U | x.1 ∈ CompFiber d ϕ J y U}}
 
/-- CH03-P06-03: 命题 3.5(ii-b) 像目标纤维相等或不交；去重后构成 `U` 的分划。 -/
theorem prop_3_5_ii_b_eq_or_disjoint_and_partition {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (J : Set I)
    (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    (∀ y₁ ∈ operator_image ϕ U, ∀ y₂ ∈ operator_image ϕ U,
      CompFiber d ϕ J y₁ U = CompFiber d ϕ J y₂ U ∨
        Disjoint (CompFiber d ϕ J y₁ U) (CompFiber d ϕ J y₂ U)) ∧
    ∅ ∉ CompFiberPartition d ϕ J U ∧
    ⋃₀ CompFiberPartition d ϕ J U = U ∧
    (CompFiberPartition d ϕ J U).PairwiseDisjoint id ∧
    Setoid.IsPartition (CompFiberSubtypePartition d ϕ J U) := by
  rcases prop_3_5_ii_a_nonempty_and_cover d hd ϕ U J hU hJ with ⟨hne, hcov⟩
  have heq_or_disj : ∀ y₁ ∈ operator_image ϕ U, ∀ y₂ ∈ operator_image ϕ U,
      CompFiber d ϕ J y₁ U = CompFiber d ϕ J y₂ U ∨
        Disjoint (CompFiber d ϕ J y₁ U) (CompFiber d ϕ J y₂ U) := by
    intro y₁ _ y₂ _
    by_cases hdisj : Disjoint (CompFiber d ϕ J y₁ U) (CompFiber d ϕ J y₂ U)
    · exact Or.inr hdisj
    · left
      rcases Set.not_disjoint_iff.mp hdisj with ⟨x, hx₁, hx₂⟩
      have h1 := (subfamily_pseudometric_eq_zero_iff d J (ϕ.func x) y₁).mp hx₁.2
      have h2 := (subfamily_pseudometric_eq_zero_iff d J (ϕ.func x) y₂).mp hx₂.2
      have hy12 : subfamily_pseudometric d J y₁ y₂ = 0 := by
        rw [subfamily_pseudometric_eq_zero_iff]
        intro j hj
        apply le_antisymm _ (zero_le _)
        calc
          d j y₁ y₂ ≤ d j y₁ (ϕ.func x) + d j (ϕ.func x) y₂ := (hd j).triangle _ _ _
          _ = 0 := by rw [(hd j).symm y₁ (ϕ.func x), h1 j hj, h2 j hj, zero_add]
      exact prop_3_5_i_target_zero_invariant d hd ϕ U J y₁ y₂ hU hJ hy12
  refine ⟨heq_or_disj, ?_, ?_, ?_, ?_⟩
  · rintro ⟨y, hy, hemp⟩
    rcases hne y hy with ⟨x, hx⟩
    rw [← hemp] at hx
    exact hx
  · ext x
    conv_rhs => rw [← hcov]
    simp only [CompFiberPartition, Set.mem_sUnion, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨F, ⟨y, hy, rfl⟩, hx⟩
      exact ⟨y, hy, hx⟩
    · rintro ⟨y, hy, hx⟩
      exact ⟨CompFiber d ϕ J y U, ⟨y, hy, rfl⟩, hx⟩
  · rintro F₁ ⟨y₁, hy₁, rfl⟩ F₂ ⟨y₂, hy₂, rfl⟩ hneF
    rcases heq_or_disj y₁ hy₁ y₂ hy₂ with heq | hdisj
    · exact False.elim (hneF heq)
    · exact hdisj
  · refine ⟨?_, ?_⟩
    · rintro ⟨y, hy, hemp⟩
      rcases hne y hy with ⟨x, hx⟩
      have hmem : (⟨x, hx.1⟩ : ↥U) ∈ (∅ : Set ↥U) := by
        rw [hemp]
        exact hx
      exact hmem
    · intro x
      have hself : subfamily_pseudometric d J (ϕ.func x.1) (ϕ.func x.1) = 0 :=
        (subfamily_pseudometric_eq_zero_iff d J _ _).mpr (fun j _ => (hd j).dist_self _)
      refine ⟨{z : ↥U | z.1 ∈ CompFiber d ϕ J (ϕ.func x.1) U}, ?_, ?_⟩
      · exact ⟨⟨ϕ.func x.1, ⟨x.1, x.2, rfl⟩, rfl⟩, ⟨x.2, hself⟩⟩
      · rintro G ⟨⟨y, hy, rfl⟩, hGx⟩
        ext z
        simp only [Set.mem_setOf_eq]
        rcases heq_or_disj y hy (ϕ.func x.1) ⟨x.1, x.2, rfl⟩ with heq | hdisj
        · rw [heq]
        · exact False.elim (Set.disjoint_left.mp hdisj hGx ⟨x.2, hself⟩)
 
/-- CH03-P06-04: 命题 3.5(iii) 有限非空子族的分量交集律。 -/
theorem prop_3_5_iii_inter_eq {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (J : Set I) (y : X)
    (_hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    CompFiber d ϕ J y U = ⋂ j ∈ J, CompFiberSingle d ϕ j y U := by
  rcases hJ with ⟨j₀, hj₀⟩
  ext x
  simp only [CompFiber, CompFiberSingle_eq, Set.mem_setOf_eq, Set.mem_iInter,
    subfamily_pseudometric_eq_zero_iff]
  constructor
  · rintro ⟨hxU, hall⟩ j hj
    exact ⟨hxU, hall j hj⟩
  · intro hall
    exact ⟨(hall j₀ hj₀).1, fun j hj => (hall j hj).2⟩
 
/-- CH03-P06-05: 命题 3.5(iv) 子族单调性（`J ⊆ K` 时纤维缩小）。 -/
theorem prop_3_5_iv_subfamily_antitone {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (J K : Set I) (y : X)
    (_hU : U ⊆ dom ϕ) (_hJ : J.Nonempty) (_hK : K.Nonempty) (hJK : J ⊆ K) :
    CompFiber d ϕ K y U ⊆ CompFiber d ϕ J y U := by
  rintro x ⟨hxU, hK0⟩
  refine ⟨hxU, ?_⟩
  rw [subfamily_pseudometric_eq_zero_iff] at hK0 ⊢
  exact fun j hj => hK0 j (hJK hj)
 
/-- CH03-P06-06: 命题 3.5(v) 子族边界（单分量等式与全子族向每分量包含）。 -/
theorem prop_3_5_v_subfamily_boundary {X I : Type} {bot : X} [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (y : X)
    (_hU : U ⊆ dom ϕ) :
    (∀ i : I, CompFiber d ϕ {i} y U = CompFiberSingle d ϕ i y U ∧
      CompFiberSingle d ϕ i y U = {x ∈ U | d i (ϕ.func x) y = 0}) ∧
    (∀ i : I, CompFiber d ϕ Set.univ y U ⊆ CompFiberSingle d ϕ i y U) := by
  refine ⟨fun i => ⟨rfl, CompFiberSingle_eq d ϕ i y U⟩, fun i => ?_⟩
  exact prop_3_5_iv_subfamily_antitone d ϕ U {i} Set.univ y _hU
    (Set.singleton_nonempty i) Set.univ_nonempty (Set.subset_univ _)
 
/-- CH03-P06-07: 命题 3.5(vi-a) 恒等分量的任意目标纤维等于输入零距类。 -/
theorem prop_3_5_vi_a_id_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (j : I) (y : X)
    (_hU : U ⊆ dom ϕ) (hj : j ∈ I_id d ϕ U) :
    CompFiberSingle d ϕ j y U = {x ∈ U | d j x y = 0} := by
  rw [CompFiberSingle_eq]
  ext x
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun hx => ⟨fun h0 => ?_, fun h0 => ?_⟩
  · apply le_antisymm _ (zero_le _)
    calc
      d j x y ≤ d j x (ϕ.func x) + d j (ϕ.func x) y := (hd j).triangle _ _ _
      _ = 0 := by rw [(hd j).symm x (ϕ.func x), hj.2 x hx, h0, zero_add]
  · apply le_antisymm _ (zero_le _)
    calc
      d j (ϕ.func x) y ≤ d j (ϕ.func x) x + d j x y := (hd j).triangle _ _ _
      _ = 0 := by rw [hj.2 x hx, h0, zero_add]
 
/-- CH03-P06-08: 命题 3.5(vi-b) 常值分量在像目标的纤维为 `U`，正距离目标的纤维为空。 -/
theorem prop_3_5_vi_b_const_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (j : I) (y₀ : X)
    (_hU : U ⊆ dom ϕ) (hj : j ∈ I_const d ϕ U) (hy₀ : y₀ ∈ operator_image ϕ U) :
    CompFiberSingle d ϕ j y₀ U = U ∧
    ∀ y : X, 0 < d j y y₀ → CompFiberSingle d ϕ j y U = ∅ := by
  rcases hy₀ with ⟨x₀, hx₀, rfl⟩
  rw [CompFiberSingle_eq]
  refine ⟨?_, ?_⟩
  · ext x
    simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
    exact fun hx => hj x hx x₀ hx₀
  · intro y hpos
    rw [CompFiberSingle_eq]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hxy
    have hzero : d j y (ϕ.func x₀) = 0 := by
      apply le_antisymm _ (zero_le _)
      calc
        d j y (ϕ.func x₀) ≤ d j y (ϕ.func x) + d j (ϕ.func x) (ϕ.func x₀) :=
          (hd j).triangle _ _ _
        _ = 0 := by rw [(hd j).symm y (ϕ.func x), hxy, hj x hx x₀ hx₀, zero_add]
    exact (ne_of_gt hpos) hzero
 
/-! ### 命题 3.6：像值因子化与标量 Lip 界 (CH03-P07-01 .. 04) -/
 
/-- 映射 `T : ϕ_A(U) → X` 在 `U` 上满足 `T ∘ ϕ_A = ϕ_B`。 -/
def IsImageFactorMap {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X) (T : ↥(operator_image ϕA U) → X) : Prop :=
  ∀ x : X, ∀ hx : x ∈ U, T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x
 
/-- CH03-P07-01: 命题 3.6(i-必要) 点值像映射存在推出相等关系包含。 -/
theorem prop_3_6_i_nec {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (_hU : U ⊆ dom ϕA ∩ dom ϕB)
    (hex : ∃ T : ↥(operator_image ϕA U) → X, IsImageFactorMap ϕA ϕB U T) :
    RelEq ϕA U ⊆ RelEq ϕB U := by
  rcases hex with ⟨T, hT⟩
  rintro ⟨x, y⟩ ⟨hx, hy, heqA⟩
  refine ⟨hx, hy, ?_⟩
  have hsub : (⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ : ↥(operator_image ϕA U)) =
      ⟨ϕA.func y, ⟨y, hy, rfl⟩⟩ := Subtype.ext heqA
  calc
    ϕB.func x = T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ := (hT x hx).symm
    _ = T ⟨ϕA.func y, ⟨y, hy, rfl⟩⟩ := congrArg T hsub
    _ = ϕB.func y := hT y hy
 
/-- 由 `ℛ_{=}(ϕ_A | U) ⊆ ℛ_{=}(ϕ_B | U)` 显式构造像值变换 `T : ϕ_A(U) → X`（含 `U = ∅` 情形）。 -/
noncomputable def constructImageFactorMap {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X) : ↥(operator_image ϕA U) → X :=
  fun y => ϕB.func (Classical.choose y.2)
 
/-- CH03-P07-02: 命题 3.6(i-充分及充要判据，含代表元无关性与 `U = ∅` 边界验证)。 -/
theorem prop_3_6_i_suf_and_iff {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕA ∩ dom ϕB) :
    (RelEq ϕA U ⊆ RelEq ϕB U →
      IsImageFactorMap ϕA ϕB U (constructImageFactorMap ϕA ϕB U) ∧
      ∀ (y : ↥(operator_image ϕA U)) (x : X), x ∈ U → ϕA.func x = y.1 →
        constructImageFactorMap ϕA ϕB U y = ϕB.func x) ∧
    ((∃ T : ↥(operator_image ϕA U) → X, IsImageFactorMap ϕA ϕB U T) ↔
      RelEq ϕA U ⊆ RelEq ϕB U) := by
  have hsuf : RelEq ϕA U ⊆ RelEq ϕB U →
      IsImageFactorMap ϕA ϕB U (constructImageFactorMap ϕA ϕB U) ∧
      ∀ (y : ↥(operator_image ϕA U)) (x : X), x ∈ U → ϕA.func x = y.1 →
        constructImageFactorMap ϕA ϕB U y = ϕB.func x := by
    intro hsub
    have hind : ∀ (y : ↥(operator_image ϕA U)) (x : X), x ∈ U → ϕA.func x = y.1 →
        constructImageFactorMap ϕA ϕB U y = ϕB.func x := by
      intro y x hx hxeq
      have hspec := Classical.choose_spec y.2
      have hrelA : (Classical.choose y.2, x) ∈ RelEq ϕA U :=
        ⟨hspec.1, hx, hspec.2.trans hxeq.symm⟩
      exact (hsub hrelA).2.2
    refine ⟨fun x hx => hind ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ x hx rfl, hind⟩
  refine ⟨hsuf, ⟨prop_3_6_i_nec ϕA ϕB U hU, fun hsub => ⟨_, (hsuf hsub).1⟩⟩⟩
 
theorem prop_3_6_i_empty_domain {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) :
    IsImageFactorMap ϕA ϕB ∅ (constructImageFactorMap ϕA ϕB ∅) ∧
    RelEq ϕA ∅ = ∅ ∧ RelEq ϕB ∅ = ∅ := by
  refine ⟨fun x hx => False.elim hx, ?_, ?_⟩ <;> ext p <;> simp [RelEq]
 
/-- CH03-P07-03: 命题 3.6(ii) 双向点值像变换存在当且仅当点值相等关系相同。 -/
theorem prop_3_6_ii_bidirectional_iff {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕA ∩ dom ϕB) :
    ((∃ TAB : ↥(operator_image ϕA U) → X, IsImageFactorMap ϕA ϕB U TAB) ∧
     (∃ TBA : ↥(operator_image ϕB U) → X, IsImageFactorMap ϕB ϕA U TBA)) ↔
      RelEq ϕA U = RelEq ϕB U := by
  have hU_symm : U ⊆ dom ϕB ∩ dom ϕA := fun x hx => ⟨(hU hx).2, (hU hx).1⟩
  rw [(prop_3_6_i_suf_and_iff ϕA ϕB U hU).2,
      (prop_3_6_i_suf_and_iff ϕB ϕA U hU_symm).2,
      Set.Subset.antisymm_iff]
 
/-- CH03-P07-04: 命题 3.6(iii) 单分量有限正 `K_A`、有限非负 `L_B` 下像值变换 `T` 在 `ϕ_A(U)` 上的 `L_B / K_A` 标量 Lip 界。 -/
theorem prop_3_6_iii_scalar_lip_bound {X : Type} {bot : X}
    (d : X → X → ENNReal) (ϕA ϕB : Operator X bot) (U : Set X)
    (T : ↥(operator_image ϕA U) → X)
    (KA LB : ENNReal)
    (_hU : U ⊆ dom ϕA ∩ dom ϕB)
    (hT : IsImageFactorMap ϕA ϕB U T)
    (hKA0 : 0 < KA) (hKAtop : KA < ⊤) (_hLBtop : LB < ⊤)
    (hCoLipA : ∀ x ∈ U, ∀ x' ∈ U, KA * d x x' ≤ d (ϕA.func x) (ϕA.func x'))
    (hLipB : ∀ x ∈ U, ∀ x' ∈ U, d (ϕB.func x) (ϕB.func x') ≤ LB * d x x') :
    ∀ y y' : ↥(operator_image ϕA U),
      d (T y) (T y') ≤ (LB / KA) * d y.1 y'.1 := by
  intro y y'
  rcases y with ⟨yv, x, hx, rfl⟩
  rcases y' with ⟨y'v, x', hx', rfl⟩
  have hKA_ne0 : KA ≠ 0 := ne_of_gt hKA0
  have hKA_netop : KA ≠ ⊤ := lt_top_iff_ne_top.mp hKAtop
  have hinv : d x x' ≤ KA⁻¹ * d (ϕA.func x) (ϕA.func x') := by
    calc
      d x x' = (KA⁻¹ * KA) * d x x' := by rw [ENNReal.inv_mul_cancel hKA_ne0 hKA_netop, one_mul]
      _ = KA⁻¹ * (KA * d x x') := mul_assoc _ _ _
      _ ≤ KA⁻¹ * d (ϕA.func x) (ϕA.func x') := mul_le_mul_right (hCoLipA x hx x' hx') _
  rw [hT x hx, hT x' hx']
  calc
    d (ϕB.func x) (ϕB.func x') ≤ LB * d x x' := hLipB x hx x' hx'
    _ ≤ LB * (KA⁻¹ * d (ϕA.func x) (ϕA.func x')) := mul_le_mul_right hinv LB
    _ = (LB / KA) * d (ϕA.func x) (ϕA.func x') := by
        rw [← mul_assoc, div_eq_mul_inv]
 
/-- CH03-P07-04 补充：单分量规范族 `[Subsingleton I]` 下从 `IsCoLipMatrix` 与 `IsLipMatrix` 接口直接读取命题 3.6(iii)。 -/
theorem prop_3_6_iii_matrix_interface {X I : Type} {bot : X} [Fintype I] [Subsingleton I]
    (d : I → X → X → ENNReal) (i : I) (ϕA ϕB : Operator X bot) (U : Set X)
    (T : ↥(operator_image ϕA U) → X)
    (K L : I → I → ENNReal)
    (hU : U ⊆ dom ϕA ∩ dom ϕB)
    (hT : IsImageFactorMap ϕA ϕB U T)
    (hK : IsCoLipMatrix d ϕA U K) (hL : IsLipMatrix d ϕB U L)
    (hK0 : 0 < K i i) (hKtop : K i i < ⊤) (hLtop : L i i < ⊤) :
    ∀ y y' : ↥(operator_image ϕA U),
      d i (T y) (T y') ≤ (L i i / K i i) * d i y.1 y'.1 := by
  apply prop_3_6_iii_scalar_lip_bound (d i) ϕA ϕB U T (K i i) (L i i) hU hT hK0 hKtop hLtop
  · intro x hx x' hx'
    have h := hK.2.2 x hx x' hx' i
    have hsum : (∑ k : I, K k i * d k x x') = K i i * d i x x' :=
      Finset.sum_eq_single i (fun k _ hk => False.elim (hk (Subsingleton.elim k i)))
        (fun hi => False.elim (hi (Finset.mem_univ i)))
    simpa [hsum] using h
  · exact single_component_lip_matrix_ineq d ϕB U L i hL
 
/-! ### 命题 3.7：零距商上的像值因子化 (CH03-P08-01 .. 03) -/
 
/-- 商映射 `Tbar : ϕ_A(U)/∼_𝒢 → ϕ_B(U)/∼_𝒢` 满足规定赋值公式 `Tbar([ϕ_A(x)]) = [ϕ_B(x)]` (`x ∈ U`)。 -/
def IsQuotientFactorMap {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (Tbar : ImageGaugeQuotient d hd ϕA U → ImageGaugeQuotient d hd ϕB U) : Prop :=
  ∀ x : X, ∀ hx : x ∈ U,
    Tbar (imageQuotientClass d hd ϕA U hx) = imageQuotientClass d hd ϕB U hx
 
/-- 由 `ℛ_{∼}(ϕ_A | U) ⊆ ℛ_{∼}(ϕ_B | U)` 通过 `Quotient.lift` 构造代表元无关的商映射。 -/
noncomputable def constructQuotientFactorMap {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hsub : RelGaugeZero d ϕA U ⊆ RelGaugeZero d ϕB U) :
    ImageGaugeQuotient d hd ϕA U → ImageGaugeQuotient d hd ϕB U :=
  Quotient.lift
    (fun y : ↥(operator_image ϕA U) =>
      imageQuotientClass d hd ϕB U (Classical.choose_spec y.2).1)
    (by
      intro y₁ y₂ hrel
      have hs₁ := Classical.choose_spec y₁.2
      have hs₂ := Classical.choose_spec y₂.2
      apply Quotient.sound
      change GaugeZeroRelated d _ _
      have hrelA : (Classical.choose y₁.2, Classical.choose y₂.2) ∈ RelGaugeZero d ϕA U := by
        refine ⟨hs₁.1, hs₂.1, ?_⟩
        rw [hs₁.2, hs₂.2]
        exact hrel
      exact (hsub hrelA).2.2)
 
/-- CH03-P08-01: 命题 3.7 单向商映射判据及显式构造验证。 -/
theorem prop_3_7_unidirectional_quotient_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (_hU : U ⊆ dom ϕA ∩ dom ϕB) :
    (∀ hsub : RelGaugeZero d ϕA U ⊆ RelGaugeZero d ϕB U,
      IsQuotientFactorMap d hd ϕA ϕB U (constructQuotientFactorMap d hd ϕA ϕB U hsub)) ∧
    ((∃ Tbar : ImageGaugeQuotient d hd ϕA U → ImageGaugeQuotient d hd ϕB U,
        IsQuotientFactorMap d hd ϕA ϕB U Tbar) ↔
      RelGaugeZero d ϕA U ⊆ RelGaugeZero d ϕB U) := by
  have hsuf : ∀ hsub : RelGaugeZero d ϕA U ⊆ RelGaugeZero d ϕB U,
      IsQuotientFactorMap d hd ϕA ϕB U (constructQuotientFactorMap d hd ϕA ϕB U hsub) := by
    intro hsub x hx
    unfold constructQuotientFactorMap imageQuotientClass
    dsimp only [Quotient.lift_mk]
    apply Quotient.sound
    change GaugeZeroRelated d _ _
    set z := Classical.choose (⟨x, hx, rfl⟩ : ∃ z ∈ U, ϕA.func z = ϕA.func x)
    have hspec : z ∈ U ∧ ϕA.func z = ϕA.func x :=
      Classical.choose_spec (⟨x, hx, rfl⟩ : ∃ z ∈ U, ϕA.func z = ϕA.func x)
    have hrelA : (z, x) ∈ RelGaugeZero d ϕA U := by
      refine ⟨hspec.1, hx, fun i => ?_⟩
      rw [hspec.2, (hd i).dist_self]
    exact (hsub hrelA).2.2
  refine ⟨hsuf, ⟨?_, fun hsub => ⟨_, hsuf hsub⟩⟩⟩
  rintro ⟨Tbar, hTbar⟩ ⟨x, y⟩ ⟨hx, hy, hzeroA⟩
  refine ⟨hx, hy, ?_⟩
  have hcls : imageQuotientClass d hd ϕA U hx = imageQuotientClass d hd ϕA U hy :=
    Quotient.sound hzeroA
  have hclsB : imageQuotientClass d hd ϕB U hx = imageQuotientClass d hd ϕB U hy := by
    rw [← hTbar x hx, ← hTbar y hy, hcls]
  exact Quotient.exact hclsB
 
/-- CH03-P08-02: 命题 3.7 双向商变换存在当且仅当零距关系相等。 -/
theorem prop_3_7_bidirectional_quotient_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕA ∩ dom ϕB) :
    ((∃ TAB : ImageGaugeQuotient d hd ϕA U → ImageGaugeQuotient d hd ϕB U,
        IsQuotientFactorMap d hd ϕA ϕB U TAB) ∧
     (∃ TBA : ImageGaugeQuotient d hd ϕB U → ImageGaugeQuotient d hd ϕA U,
        IsQuotientFactorMap d hd ϕB ϕA U TBA)) ↔
      RelGaugeZero d ϕA U = RelGaugeZero d ϕB U := by
  have hU_symm : U ⊆ dom ϕB ∩ dom ϕA := fun x hx => ⟨(hU hx).2, (hU hx).1⟩
  rw [(prop_3_7_unidirectional_quotient_iff d hd ϕA ϕB U hU).2,
      (prop_3_7_unidirectional_quotient_iff d hd ϕB ϕA U hU_symm).2,
      Set.Subset.antisymm_iff]
 
/-- 仅在实际像集 `ϕ(U)` 上分离时，`ℛ_{=}(ϕ | U) = ℛ_{∼}(ϕ | U)`。 -/
theorem RelEq_eq_RelGaugeZero_of_separatingOn_image {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X)
    (hsep : IsSeparatingOn d (operator_image ϕ U)) :
    RelEq ϕ U = RelGaugeZero d ϕ U := by
  ext ⟨x, y⟩
  simp only [RelEq, RelGaugeZero, Set.mem_setOf_eq]
  refine and_congr_right fun hx => and_congr_right fun hy => ⟨?_, ?_⟩
  · intro heq i
    rw [heq, (hd i).dist_self]
  · intro hzero
    exact hsep (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩ hzero
 
/-- CH03-P08-03: 命题 3.7 仅在两个实际像集 `ϕ_A(U)` 与 `ϕ_B(U)` 各自分离的条件下，点值判据与商判据一致。 -/
theorem prop_3_7_separating_image_equivalence {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕA ∩ dom ϕB)
    (hsepA : IsSeparatingOn d (operator_image ϕA U))
    (hsepB : IsSeparatingOn d (operator_image ϕB U)) :
    RelEq ϕA U = RelGaugeZero d ϕA U ∧
    RelEq ϕB U = RelGaugeZero d ϕB U ∧
    ((∃ T : ↥(operator_image ϕA U) → X, IsImageFactorMap ϕA ϕB U T) ↔
      (∃ Tbar : ImageGaugeQuotient d hd ϕA U → ImageGaugeQuotient d hd ϕB U,
        IsQuotientFactorMap d hd ϕA ϕB U Tbar)) ∧
    (((∃ TAB : ↥(operator_image ϕA U) → X, IsImageFactorMap ϕA ϕB U TAB) ∧
      (∃ TBA : ↥(operator_image ϕB U) → X, IsImageFactorMap ϕB ϕA U TBA)) ↔
     ((∃ TAB : ImageGaugeQuotient d hd ϕA U → ImageGaugeQuotient d hd ϕB U,
        IsQuotientFactorMap d hd ϕA ϕB U TAB) ∧
      (∃ TBA : ImageGaugeQuotient d hd ϕB U → ImageGaugeQuotient d hd ϕA U,
        IsQuotientFactorMap d hd ϕB ϕA U TBA))) := by
  have heqA := RelEq_eq_RelGaugeZero_of_separatingOn_image d hd ϕA U hsepA
  have heqB := RelEq_eq_RelGaugeZero_of_separatingOn_image d hd ϕB U hsepB
  refine ⟨heqA, heqB, ?_, ?_⟩
  · rw [(prop_3_6_i_suf_and_iff ϕA ϕB U hU).2,
        (prop_3_7_unidirectional_quotient_iff d hd ϕA ϕB U hU).2, heqA, heqB]
  · rw [prop_3_6_ii_bidirectional_iff ϕA ϕB U hU,
        prop_3_7_bidirectional_quotient_iff d hd ϕA ϕB U hU, heqA, heqB]
 
/-! ### 注：纤维包含的传递 (CH03-P09-01 .. 03) -/
 
/-- CH03-P09-01: 固定公共评估域 `U` 的零测距纤维预序满足自反性与传递性。 -/
theorem note_fiber_preorder_refl_trans {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) :
    (∀ ϕ : Operator X bot, U ⊆ dom ϕ → FiberPreorder d U ϕ ϕ) ∧
    (∀ ϕ₁ ϕ₂ ϕ₃ : Operator X bot,
      U ⊆ dom ϕ₁ → U ⊆ dom ϕ₂ → U ⊆ dom ϕ₃ →
      FiberPreorder d U ϕ₁ ϕ₂ → FiberPreorder d U ϕ₂ ϕ₃ → FiberPreorder d U ϕ₁ ϕ₃) :=
  ⟨fun _ _ => Set.Subset.refl _,
   fun _ _ _ _ _ _ h12 h23 => Set.Subset.trans h12 h23⟩
 
instance instPreorderFiberOnDomain {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) :
    Preorder {ϕ : Operator X bot // U ⊆ dom ϕ} where
  le a b := FiberPreorder d U a.1 b.1
  le_refl _ := Set.Subset.refl _
  le_trans _ _ _ h12 h23 := Set.Subset.trans h12 h23
 
/-- CH03-P09-02: 公共评估域上的有限链任意两层 `0 ≤ a < b ≤ m`（及 `a ≤ b`）满足 `ϕ_a ⪰_{fiber, U} ϕ_b`。 -/
theorem note_fiber_preorder_chain_le {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) {m : ℕ}
    (ϕs : Fin (m + 1) → Operator X bot)
    (_hdom : ∀ r : Fin (m + 1), U ⊆ dom (ϕs r))
    (hstep : ∀ r : Fin m, FiberPreorder d U (ϕs r.castSucc) (ϕs r.succ)) :
    (∀ a b : Fin (m + 1), a ≤ b → FiberPreorder d U (ϕs a) (ϕs b)) ∧
    (∀ a b : Fin (m + 1), a < b → FiberPreorder d U (ϕs a) (ϕs b)) := by
  have hle : ∀ a b : Fin (m + 1), a ≤ b → FiberPreorder d U (ϕs a) (ϕs b) := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    change a ≤ b at hab
    induction b with
    | zero =>
        have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
        subst ha0
        exact Set.Subset.refl _
    | succ k ih =>
        rcases Nat.of_le_succ hab with hk | rfl
        · have hklt : k < m + 1 := Nat.lt_of_succ_lt hb
          have h1 := ih hklt hk
          have h2 := hstep ⟨k, Nat.lt_of_succ_lt_succ hb⟩
          exact Set.Subset.trans h1 h2
        · exact Set.Subset.refl _
  exact ⟨hle, fun a b hab => hle a b (le_of_lt hab)⟩
 
/-- CH03-P09-03: 链中某一步严格包含推出首尾端点严格包含，并显式给出差集见证。 -/
theorem note_fiber_preorder_chain_strict {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) {m : ℕ}
    (ϕs : Fin (m + 1) → Operator X bot)
    (hdom : ∀ r : Fin (m + 1), U ⊆ dom (ϕs r))
    (hstep : ∀ r : Fin m, FiberPreorder d U (ϕs r.castSucc) (ϕs r.succ))
    (r : Fin m)
    (hstrict : RelGaugeZero d (ϕs r.castSucc) U ⊂ RelGaugeZero d (ϕs r.succ) U) :
    (∃ p : X × X,
      p ∈ RelGaugeZero d (ϕs r.succ) U \ RelGaugeZero d (ϕs r.castSucc) U ∧
      p ∈ RelGaugeZero d (ϕs (Fin.last m)) U \ RelGaugeZero d (ϕs 0) U) ∧
    RelGaugeZero d (ϕs 0) U ⊂ RelGaugeZero d (ϕs (Fin.last m)) U := by
  have hle := (note_fiber_preorder_chain_le d U ϕs hdom hstep).1
  have h0_le : RelGaugeZero d (ϕs 0) U ⊆ RelGaugeZero d (ϕs r.castSucc) U :=
    hle 0 r.castSucc (Fin.zero_le _)
  have h_le_last : RelGaugeZero d (ϕs r.succ) U ⊆ RelGaugeZero d (ϕs (Fin.last m)) U :=
    hle r.succ (Fin.last m) (Fin.le_last _)
  have h0_last : RelGaugeZero d (ϕs 0) U ⊆ RelGaugeZero d (ϕs (Fin.last m)) U :=
    hle 0 (Fin.last m) (Fin.zero_le _)
  rcases Set.exists_of_ssubset hstrict with ⟨p, hpin, hpout⟩
  have hp_end : p ∈ RelGaugeZero d (ϕs (Fin.last m)) U \ RelGaugeZero d (ϕs 0) U :=
    ⟨h_le_last hpin, fun hp0 => hpout (h0_le hp0)⟩
  refine ⟨⟨p, ⟨hpin, hpout⟩, hp_end⟩, Set.ssubset_iff_subset_ne.mpr ⟨h0_last, ?_⟩⟩
  intro heq
  rw [heq] at hp_end
  exact hp_end.2 hp_end.1
 
end Ch03
