import Ch03.Defs
import Ch03.Sec1_ComponentPartition

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

/-!
# § 3.2 计算纤维与像值因子化 (`CH03-P06-01` – `CH03-P09-03`)
-/

/-! ## 命题 3.5：计算纤维的基本性质 (`CH03-P06-01` – `CH03-P06-08`) -/

/-- `CH03-P06-01`：命题 3.5(i) — 目标零距不变性：若 `d_J(y, y') = 0`，则 `Fib_{ϕ, J}(y | U) = Fib_{ϕ, J}(y' | U)`。 -/
theorem prop_3_5_target_zero_invariant {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (J : Set I) (y y' : X)
    (hU : U ⊆ dom ϕ) (hJ : J.Nonempty)
    (hyy' : subfamily_pseudometric d J y y' = 0) :
    compFiber d ϕ J y U = compFiber d ϕ J y' U := by
  have _ := hU
  have hzero_yy' : ∀ j ∈ J, d j y y' = 0 :=
    (subfamily_pseudometric_eq_zero_iff d J hJ y y').mp hyy'
  ext x
  simp only [compFiber, Set.mem_setOf_eq, subfamily_pseudometric_eq_zero_iff d J hJ]
  constructor
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, fun j hj => ?_⟩
    apply le_antisymm _ (zero_le _)
    calc
      d j (ϕ.func x) y' ≤ d j (ϕ.func x) y + d j y y' := (hd j).triangle _ _ _
      _ = 0 := by simp [hxy j hj, hzero_yy' j hj]
  · rintro ⟨hx, hxy'⟩
    refine ⟨hx, fun j hj => ?_⟩
    apply le_antisymm _ (zero_le _)
    have hy'y : d j y' y = 0 := by rw [(hd j).symm y' y, hzero_yy' j hj]
    calc
      d j (ϕ.func x) y ≤ d j (ϕ.func x) y' + d j y' y := (hd j).triangle _ _ _
      _ = 0 := by simp [hxy' j hj, hy'y]

/-- `CH03-P06-02`：命题 3.5(ii-a) — 像集 `ϕ(U)` 中任一目标对应的纤维均非空，且全体像目标纤维覆盖 `U`。 -/
theorem prop_3_5_image_fibers_nonempty_and_cover {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (J : Set I)
    (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    (∀ y ∈ operator_image ϕ U, (compFiber d ϕ J y U).Nonempty) ∧
    (⋃ y ∈ operator_image ϕ U, compFiber d ϕ J y U) = U := by
  have _ := hU
  have hself : ∀ x : X, subfamily_pseudometric d J (ϕ.func x) (ϕ.func x) = 0 := by
    intro x
    exact (subfamily_pseudometric_eq_zero_iff d J hJ _ _).mpr
      (fun j _ => (hd j).dist_self (ϕ.func x))
  refine ⟨?_, ?_⟩
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, hself x⟩
  · ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨_, _, hx, _⟩
      exact hx
    · intro hx
      exact ⟨ϕ.func x, ⟨x, hx, rfl⟩, hx, hself x⟩

/-- 集合族 `P` 构成集合 `U` 的分划：不含空集、并集为 `U`、不同块两两不交。 -/
def IsSetPartition {X : Type} (P : Set (Set X)) (U : Set X) : Prop :=
  ∅ ∉ P ∧ ⋃₀ P = U ∧ P.PairwiseDisjoint id

/-- 将相同像目标纤维去重后得到的集合族 `{ Fib_{ϕ, J}(y | U) : y ∈ ϕ(U) }`。 -/
def fiberPartitionFamily {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (J : Set I) (U : Set X) : Set (Set X) :=
  { F : Set X | ∃ y ∈ operator_image ϕ U, F = compFiber d ϕ J y U }

/-- `CH03-P06-03`：命题 3.5(ii-b) — 像目标纤维要么相等要么不交，去重后的纤维集合族构成 `U` 的分划。 -/
theorem prop_3_5_image_fibers_dichotomy_and_partition {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (J : Set I)
    (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    (∀ y₁ ∈ operator_image ϕ U, ∀ y₂ ∈ operator_image ϕ U,
      compFiber d ϕ J y₁ U = compFiber d ϕ J y₂ U ∨
        Disjoint (compFiber d ϕ J y₁ U) (compFiber d ϕ J y₂ U)) ∧
    IsSetPartition (fiberPartitionFamily d ϕ J U) U := by
  have hdich : ∀ y₁ ∈ operator_image ϕ U, ∀ y₂ ∈ operator_image ϕ U,
      compFiber d ϕ J y₁ U = compFiber d ϕ J y₂ U ∨
        Disjoint (compFiber d ϕ J y₁ U) (compFiber d ϕ J y₂ U) := by
    intro y₁ _ y₂ _
    by_cases hdisj : Disjoint (compFiber d ϕ J y₁ U) (compFiber d ϕ J y₂ U)
    · exact Or.inr hdisj
    · left
      rw [Set.not_disjoint_iff] at hdisj
      rcases hdisj with ⟨x, hx₁, hx₂⟩
      have h1 := (subfamily_pseudometric_eq_zero_iff d J hJ _ _).mp hx₁.2
      have h2 := (subfamily_pseudometric_eq_zero_iff d J hJ _ _).mp hx₂.2
      have hy₁₂ : subfamily_pseudometric d J y₁ y₂ = 0 := by
        rw [subfamily_pseudometric_eq_zero_iff d J hJ]
        intro j hj
        apply le_antisymm _ (zero_le _)
        have hsymm : d j y₁ (ϕ.func x) = 0 := by rw [(hd j).symm, h1 j hj]
        calc
          d j y₁ y₂ ≤ d j y₁ (ϕ.func x) + d j (ϕ.func x) y₂ := (hd j).triangle _ _ _
          _ = 0 := by simp [hsymm, h2 j hj]
      exact prop_3_5_target_zero_invariant d hd ϕ U J y₁ y₂ hU hJ hy₁₂
  obtain ⟨hne, hcov⟩ := prop_3_5_image_fibers_nonempty_and_cover d hd ϕ U J hU hJ
  refine ⟨hdich, ?_, ?_, ?_⟩
  · rintro ⟨y, hy, hemp⟩
    rcases hne y hy with ⟨x, hx⟩
    rw [← hemp] at hx
    exact hx
  · refine Eq.trans ?_ hcov
    ext x
    simp only [Set.mem_sUnion, fiberPartitionFamily, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨F, ⟨y, hy, rfl⟩, hx⟩
      exact ⟨y, hy, hx⟩
    · rintro ⟨y, hy, hx⟩
      exact ⟨compFiber d ϕ J y U, ⟨y, hy, rfl⟩, hx⟩
  · rintro F₁ ⟨y₁, hy₁, rfl⟩ F₂ ⟨y₂, hy₂, rfl⟩ hne_F
    rcases hdich y₁ hy₁ y₂ hy₂ with heq | hdisj
    · exact False.elim (hne_F heq)
    · exact hdisj

/-- `CH03-P06-04`：命题 3.5(iii) — 有限非空子族的分量交集律：
`Fib_{ϕ, J}(y | U) = ⋂_{j ∈ J} Fib_{ϕ, j}(y | U)`。 -/
theorem prop_3_5_compFiber_biInter {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (J : Set I) (y : X)
    (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) :
    compFiber d ϕ J y U = ⋂ j ∈ J, singleCompFiber d ϕ j y U := by
  have _ := hU
  rcases hJ with ⟨j₀, hj₀⟩
  ext x
  simp only [compFiber, singleCompFiber, Set.mem_setOf_eq, Set.mem_iInter,
    subfamily_pseudometric_eq_zero_iff d J ⟨j₀, hj₀⟩]
  constructor
  · rintro ⟨hx, hall⟩ j hj
    exact ⟨hx, hall j hj⟩
  · intro hall
    exact ⟨(hall j₀ hj₀).1, fun j hj => (hall j hj).2⟩

/-- `CH03-P06-05`：命题 3.5(iv) — 子族单调性：若非空子族满足 `J ⊆ K`，则 `Fib_{ϕ, K}(y | U) ⊆ Fib_{ϕ, J}(y | U)`。 -/
theorem prop_3_5_compFiber_antitone {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (J K : Set I) (y : X)
    (hU : U ⊆ dom ϕ) (hJ : J.Nonempty) (hK : K.Nonempty) (hJK : J ⊆ K) :
    compFiber d ϕ K y U ⊆ compFiber d ϕ J y U := by
  have _ := hU
  intro x hx
  simp only [compFiber, Set.mem_setOf_eq,
    subfamily_pseudometric_eq_zero_iff d K hK,
    subfamily_pseudometric_eq_zero_iff d J hJ] at hx ⊢
  exact ⟨hx.1, fun j hj => hx.2 j (hJK hj)⟩

/-- `CH03-P06-06`：命题 3.5(v) — 子族边界：单分量等式 `J = {i}` 及全子族 `J = I` 向每个单分量纤维的包含。 -/
theorem prop_3_5_subfamily_boundaries {X I : Type} {bot : X} [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (i : I) (y : X) (hU : U ⊆ dom ϕ) :
    compFiber d ϕ ({i} : Set I) y U = singleCompFiber d ϕ i y U ∧
    singleCompFiber d ϕ i y U = { x ∈ U | d i (ϕ.func x) y = 0 } ∧
    compFiber d ϕ (Set.univ : Set I) y U ⊆ singleCompFiber d ϕ i y U := by
  refine ⟨compFiber_singleton_eq d ϕ i y U, rfl, ?_⟩
  rw [← compFiber_singleton_eq d ϕ i y U]
  exact prop_3_5_compFiber_antitone d ϕ U ({i} : Set I) Set.univ y hU
    (Set.singleton_nonempty i) Set.univ_nonempty (Set.subset_univ _)

/-- `CH03-P06-07`：命题 3.5(vi-a) — 恒等分量边界：若 `j ∈ I_id(ϕ | U)`，则对任意目标 `y`，`Fib_{ϕ, j}(y | U) = {x ∈ U : d_j(x, y) = 0}`。 -/
theorem prop_3_5_id_component_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (j : I) (y : X)
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hU : U ⊆ dom ϕ) (hj : j ∈ idComponents d ϕ U) :
    singleCompFiber d ϕ j y U = { x ∈ U | d j x y = 0 } := by
  have _ := hU
  ext x
  simp only [singleCompFiber, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hφy⟩
    refine ⟨hx, ?_⟩
    apply le_antisymm _ (zero_le _)
    have hxφ : d j x (ϕ.func x) = 0 := by rw [hdj.symm x (ϕ.func x), hj.2 x hx]
    calc
      d j x y ≤ d j x (ϕ.func x) + d j (ϕ.func x) y := hdj.triangle _ _ _
      _ = 0 := by simp [hxφ, hφy]
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, ?_⟩
    apply le_antisymm _ (zero_le _)
    calc
      d j (ϕ.func x) y ≤ d j (ϕ.func x) x + d j x y := hdj.triangle _ _ _
      _ = 0 := by simp [hj.2 x hx, hxy]

/-- `CH03-P06-08`：命题 3.5(vi-b) — 常值分量边界：若 `j ∈ I_const(ϕ | U)` 且 `y₀ ∈ ϕ(U)`，则 `Fib_{ϕ, j}(y₀ | U) = U`；对 `d_j(y, y₀) > 0` 的目标 `y`，纤维为空。 -/
theorem prop_3_5_const_component_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (j : I) (y₀ : X)
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hU : U ⊆ dom ϕ) (hj : j ∈ constComponents d ϕ U)
    (hy₀ : y₀ ∈ operator_image ϕ U) :
    singleCompFiber d ϕ j y₀ U = U ∧
    (∀ y : X, 0 < d j y y₀ → singleCompFiber d ϕ j y U = ∅) := by
  have _ := hU
  rcases hy₀ with ⟨x₀, hx₀, rfl⟩
  refine ⟨?_, ?_⟩
  · ext x
    simp only [singleCompFiber, Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro hx
    exact hj x hx x₀ hx₀
  · intro y hy_pos
    ext x
    simp only [singleCompFiber, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx, hφy⟩
    have hφy₀ : d j (ϕ.func x) (ϕ.func x₀) = 0 := hj x hx x₀ hx₀
    have hyφ : d j y (ϕ.func x) = 0 := by rw [hdj.symm y (ϕ.func x), hφy]
    have hle : d j y (ϕ.func x₀) ≤ 0 := by
      calc
        d j y (ϕ.func x₀) ≤ d j y (ϕ.func x) + d j (ϕ.func x) (ϕ.func x₀) :=
          hdj.triangle _ _ _
        _ = 0 := by simp [hyφ, hφy₀]
    exact (not_lt_of_ge hle) hy_pos

/-! ## 命题 3.6：像值因子化与标量 Lip 界 (`CH03-P07-01` – `CH03-P07-04`) -/

/-- 点值像映射 `T : ϕ_A(U) → X` 在 `U` 上满足 `T ∘ ϕ_A = ϕ_B`。 -/
def FactorsThroughImage {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X) (T : operator_image ϕA U → X) : Prop :=
  ∀ x (hx : x ∈ U), T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ = ϕB.func x

/-- `CH03-P07-01`：命题 3.6(i-必要) — 点值像映射存在推出点值相等关系包含 `R_=(ϕ_A | U) ⊆ R_=(ϕ_B | U)`。 -/
theorem prop_3_6_necessity {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hdom : U ⊆ dom ϕA ∩ dom ϕB)
    (hex : ∃ T : operator_image ϕA U → X, FactorsThroughImage ϕA ϕB U T) :
    relEq ϕA U ⊆ relEq ϕB U := by
  have _ := hdom
  rcases hex with ⟨T, hT⟩
  rintro ⟨x, y⟩ ⟨hx, hy, heqA⟩
  refine ⟨hx, hy, ?_⟩
  have hsub : (⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ : operator_image ϕA U) =
      ⟨ϕA.func y, ⟨y, hy, rfl⟩⟩ := Subtype.ext heqA
  calc
    ϕB.func x = T ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ := (hT x hx).symm
    _ = T ⟨ϕA.func y, ⟨y, hy, rfl⟩⟩ := congrArg T hsub
    _ = ϕB.func y := hT y hy

/-- 由 `R_=(ϕ_A | U) ⊆ R_=(ϕ_B | U)` 在实际像集 `ϕ_A(U)` 上构造的点值因子映射（自然兼容 `U = ∅`）。 -/
noncomputable def pointwiseFactorMap {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X) :
    operator_image ϕA U → X :=
  fun y => ϕB.func (Classical.choose y.2)

/-- `CH03-P07-02`：命题 3.6(i-充分) — 由 `R_=(ϕ_A | U) ⊆ R_=(ϕ_B | U)` 构造的 `pointwiseFactorMap` 对代表元选取良定义，并在 `U`（含空集）上满足 `T ∘ ϕ_A = ϕ_B`。 -/
theorem prop_3_6_sufficiency {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hdom : U ⊆ dom ϕA ∩ dom ϕB)
    (hsub : relEq ϕA U ⊆ relEq ϕB U) :
    (∀ (y : operator_image ϕA U) (x : X), x ∈ U → y.1 = ϕA.func x →
      pointwiseFactorMap ϕA ϕB U y = ϕB.func x) ∧
    FactorsThroughImage ϕA ϕB U (pointwiseFactorMap ϕA ϕB U) := by
  have _ := hdom
  have hwd : ∀ (y : operator_image ϕA U) (x : X), x ∈ U → y.1 = ϕA.func x →
      pointwiseFactorMap ϕA ϕB U y = ϕB.func x := by
    intro y x hx hyx
    have hx₀_spec := Classical.choose_spec y.2
    have hrelA : (Classical.choose y.2, x) ∈ relEq ϕA U :=
      ⟨hx₀_spec.1, hx, hx₀_spec.2.trans hyx⟩
    exact (hsub hrelA).2.2
  exact ⟨hwd, fun x hx => hwd ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩ x hx rfl⟩

/-- 命题 3.6(i) 完整充要条件。 -/
theorem prop_3_6_pointwise_factorization_iff {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hdom : U ⊆ dom ϕA ∩ dom ϕB) :
    (∃ T : operator_image ϕA U → X, FactorsThroughImage ϕA ϕB U T) ↔
      relEq ϕA U ⊆ relEq ϕB U := by
  constructor
  · exact prop_3_6_necessity ϕA ϕB U hdom
  · intro hsub
    exact ⟨pointwiseFactorMap ϕA ϕB U, (prop_3_6_sufficiency ϕA ϕB U hdom hsub).2⟩

/-- `CH03-P07-03`：命题 3.6(ii) — 两个方向的点值像变换均存在，当且仅当 `R_=(ϕ_A | U) = R_=(ϕ_B | U)`。 -/
theorem prop_3_6_bidirectional_iff {X : Type} {bot : X}
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hdom : U ⊆ dom ϕA ∩ dom ϕB) :
    ((∃ TAB : operator_image ϕA U → X, FactorsThroughImage ϕA ϕB U TAB) ∧
      (∃ TBA : operator_image ϕB U → X, FactorsThroughImage ϕB ϕA U TBA)) ↔
      relEq ϕA U = relEq ϕB U := by
  have hdom_symm : U ⊆ dom ϕB ∩ dom ϕA := fun x hx => ⟨(hdom hx).2, (hdom hx).1⟩
  rw [prop_3_6_pointwise_factorization_iff ϕA ϕB U hdom,
    prop_3_6_pointwise_factorization_iff ϕB ϕA U hdom_symm]
  exact ⟨fun ⟨h₁, h₂⟩ => Set.Subset.antisymm h₁ h₂, fun heq => ⟨heq.le, heq.ge⟩⟩

/-- `CH03-P07-04`：命题 3.6(iii) — 单分量情形下，若 `T` 存在且 `ϕ_A` 为有限正 `K_A`-co-Lip、`ϕ_B` 为有限 `L_B`-Lip，则 `T` 在实际像域 `ϕ_A(U)` 上满足 `(L_B / K_A)`-Lip 标量界。 -/
theorem prop_3_6_scalar_lip_bound {X : Type} {bot : X}
    (d : X → X → ENNReal)
    (ϕA ϕB : Operator X bot) (U : Set X)
    (T : operator_image ϕA U → X)
    (KA LB : ENNReal)
    (hdom : U ⊆ dom ϕA ∩ dom ϕB)
    (hT : FactorsThroughImage ϕA ϕB U T)
    (hKA_pos : 0 < KA) (hKA_fin : KA < ⊤) (hLB_fin : LB < ⊤)
    (hcoLipA : ∀ x ∈ U, ∀ x' ∈ U, KA * d x x' ≤ d (ϕA.func x) (ϕA.func x'))
    (hLipB : ∀ x ∈ U, ∀ x' ∈ U, d (ϕB.func x) (ϕB.func x') ≤ LB * d x x') :
    ∀ y y' : operator_image ϕA U,
      d (T y) (T y') ≤ (LB / KA) * d y.1 y'.1 := by
  have _ := hdom
  have _ := hLB_fin
  intro y y'
  rcases y with ⟨yv, x, hx, rfl⟩
  rcases y' with ⟨yv', x', hx', rfl⟩
  rw [hT x hx, hT x' hx']
  have hKA_ne0 : KA ≠ 0 := ne_of_gt hKA_pos
  have hKA_netop : KA ≠ ⊤ := ne_of_lt hKA_fin
  have hdx : d x x' ≤ d (ϕA.func x) (ϕA.func x') / KA := by
    calc
      d x x' = d x x' * (KA * KA⁻¹) := by
        rw [ENNReal.mul_inv_cancel hKA_ne0 hKA_netop, mul_one]
      _ = (KA * d x x') / KA := by
        simp only [div_eq_mul_inv]
        ac_rfl
      _ ≤ d (ϕA.func x) (ϕA.func x') / KA :=
        ENNReal.div_le_div_right (hcoLipA x hx x' hx') KA
  calc
    d (ϕB.func x) (ϕB.func x')
        ≤ LB * d x x' := hLipB x hx x' hx'
    _ ≤ LB * (d (ϕA.func x) (ϕA.func x') / KA) :=
        mul_le_mul_of_nonneg_left hdx (zero_le LB)
    _ = (LB / KA) * d (ϕA.func x) (ϕA.func x') := by
        simp only [div_eq_mul_inv]
        ac_rfl

/-- `CH03-P07-04`（单分量指标集矩阵接口特化）：`[Subsingleton I]` 下由 `IsCoLipMatrix` 与 `IsLipMatrix` 推出 `(L_B / K_A)`-Lip 标量界。 -/
theorem prop_3_6_scalar_lip_bound_matrix {X I : Type} {bot : X}
    [Fintype I] [Subsingleton I]
    (d : I → X → X → ENNReal) (i : I)
    (ϕA ϕB : Operator X bot) (U : Set X)
    (T : operator_image ϕA U → X)
    (KA LB : I → I → ENNReal)
    (hdom : U ⊆ dom ϕA ∩ dom ϕB)
    (hT : FactorsThroughImage ϕA ϕB U T)
    (hKA_pos : 0 < KA i i) (hKA_fin : KA i i < ⊤) (hLB_fin : LB i i < ⊤)
    (hK : IsCoLipMatrix d ϕA U KA)
    (hL : IsLipMatrix d ϕB U LB) :
    ∀ y y' : operator_image ϕA U,
      d i (T y) (T y') ≤ (LB i i / KA i i) * d i y.1 y'.1 := by
  apply prop_3_6_scalar_lip_bound (d i) ϕA ϕB U T (KA i i) (LB i i)
    hdom hT hKA_pos hKA_fin hLB_fin
  · intro x hx x' hx'
    have hsum := hK.2.2 x hx x' hx' i
    have hsingle : KA i i * d i x x' ≤ ∑ k : I, KA k i * d k x x' :=
      Finset.single_le_sum (f := fun k : I => KA k i * d k x x')
        (fun k _ => zero_le _) (Finset.mem_univ i)
    exact le_trans hsingle hsum
  · exact single_component_lip_matrix_ineq d ϕB U LB i hL

/-! ## 命题 3.7：零距商上的像值因子化 (`CH03-P08-01` – `CH03-P08-03`) -/

/-- 商映射 `\overline{T} : ϕ_A(U)/∼_G → ϕ_B(U)/∼_G` 满足正文规定赋值公式 `\overline{T}([ϕ_A(x)]) = [ϕ_B(x)]` (`x ∈ U`)。 -/
def QuotientFactorsThroughImage {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (Tbar : ImageZeroQuotient d hd ϕA U → ImageZeroQuotient d hd ϕB U) : Prop :=
  ∀ x (hx : x ∈ U),
    Tbar (imageZeroQuotMk d hd ϕA U x hx) = imageZeroQuotMk d hd ϕB U x hx

/-- 在 `R_∼(ϕ_A | U) ⊆ R_∼(ϕ_B | U)` 前提下，经 `Quotient.lift` 构造的代表元无关商因子映射。 -/
noncomputable def quotientFactorMap {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hsub : relZero d ϕA U ⊆ relZero d ϕB U) :
    ImageZeroQuotient d hd ϕA U → ImageZeroQuotient d hd ϕB U :=
  Quotient.lift
    (fun y : operator_image ϕA U =>
      imageZeroQuotMk d hd ϕB U (Classical.choose y.2) (Classical.choose_spec y.2).1)
    (by
      intro y₁ y₂ hrel
      apply Quotient.sound
      have hx₁ := Classical.choose_spec y₁.2
      have hx₂ := Classical.choose_spec y₂.2
      change GaugeZeroRelated d
        (ϕB.func (Classical.choose y₁.2)) (ϕB.func (Classical.choose y₂.2))
      have hrelA : (Classical.choose y₁.2, Classical.choose y₂.2) ∈ relZero d ϕA U := by
        refine ⟨hx₁.1, hx₂.1, ?_⟩
        intro i
        rw [hx₁.2, hx₂.2]
        exact hrel i
      exact (hsub hrelA).2.2)

/-- `CH03-P08-01`（构造与代表元无关验证）：`quotientFactorMap` 满足规定赋值公式 `\overline{T}([ϕ_A(x)]) = [ϕ_B(x)]`。 -/
theorem quotientFactorMap_spec {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hdom : U ⊆ dom ϕA ∩ dom ϕB)
    (hsub : relZero d ϕA U ⊆ relZero d ϕB U) :
    QuotientFactorsThroughImage d hd ϕA ϕB U (quotientFactorMap d hd ϕA ϕB U hsub) := by
  have _ := hdom
  intro x hx
  unfold quotientFactorMap imageZeroQuotMk
  rw [Quotient.lift_mk]
  apply Quotient.sound
  set y : operator_image ϕA U := ⟨ϕA.func x, ⟨x, hx, rfl⟩⟩
  have hx₀ := Classical.choose_spec y.2
  have hrelA : (Classical.choose y.2, x) ∈ relZero d ϕA U := by
    refine ⟨hx₀.1, hx, ?_⟩
    intro i
    rw [hx₀.2]
    exact (hd i).dist_self (ϕA.func x)
  exact (hsub hrelA).2.2

/-- `CH03-P08-01`：命题 3.7（单向商映射判据）— 满足规定公式的商映射存在当且仅当 `R_∼(ϕ_A | U) ⊆ R_∼(ϕ_B | U)`。 -/
theorem prop_3_7_quotient_factorization_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hdom : U ⊆ dom ϕA ∩ dom ϕB) :
    (∃ Tbar : ImageZeroQuotient d hd ϕA U → ImageZeroQuotient d hd ϕB U,
      QuotientFactorsThroughImage d hd ϕA ϕB U Tbar) ↔
      relZero d ϕA U ⊆ relZero d ϕB U := by
  constructor
  · rintro ⟨Tbar, hTbar⟩ ⟨x, y⟩ ⟨hx, hy, hrelA⟩
    refine ⟨hx, hy, ?_⟩
    have hqA : imageZeroQuotMk d hd ϕA U x hx = imageZeroQuotMk d hd ϕA U y hy :=
      Quotient.sound hrelA
    have hqB : imageZeroQuotMk d hd ϕB U x hx = imageZeroQuotMk d hd ϕB U y hy := by
      calc
        imageZeroQuotMk d hd ϕB U x hx
            = Tbar (imageZeroQuotMk d hd ϕA U x hx) := (hTbar x hx).symm
        _ = Tbar (imageZeroQuotMk d hd ϕA U y hy) := congrArg Tbar hqA
        _ = imageZeroQuotMk d hd ϕB U y hy := hTbar y hy
    exact Quotient.exact hqB
  · intro hsub
    exact ⟨quotientFactorMap d hd ϕA ϕB U hsub,
      quotientFactorMap_spec d hd ϕA ϕB U hdom hsub⟩

/-- `CH03-P08-02`：命题 3.7（双向商映射判据）— 按规定赋值公式诱导的双向商变换存在当且仅当 `R_∼(ϕ_A | U) = R_∼(ϕ_B | U)`。 -/
theorem prop_3_7_bidirectional_quotient_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hdom : U ⊆ dom ϕA ∩ dom ϕB) :
    ((∃ TAB : ImageZeroQuotient d hd ϕA U → ImageZeroQuotient d hd ϕB U,
        QuotientFactorsThroughImage d hd ϕA ϕB U TAB) ∧
      (∃ TBA : ImageZeroQuotient d hd ϕB U → ImageZeroQuotient d hd ϕA U,
        QuotientFactorsThroughImage d hd ϕB ϕA U TBA)) ↔
      relZero d ϕA U = relZero d ϕB U := by
  have hdom_symm : U ⊆ dom ϕB ∩ dom ϕA := fun x hx => ⟨(hdom hx).2, (hdom hx).1⟩
  rw [prop_3_7_quotient_factorization_iff d hd ϕA ϕB U hdom,
    prop_3_7_quotient_factorization_iff d hd ϕB ϕA U hdom_symm]
  exact ⟨fun ⟨h₁, h₂⟩ => Set.Subset.antisymm h₁ h₂, fun heq => ⟨heq.le, heq.ge⟩⟩

/-- 仅在单个实际像集 `ϕ(U)` 上分离时，`R_=(ϕ | U) = R_∼(ϕ | U)`。 -/
theorem relEq_eq_relZero_of_separatingOn_image {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X)
    (hsep : IsSeparatingOn d (operator_image ϕ U)) :
    relEq ϕ U = relZero d ϕ U := by
  ext ⟨x, y⟩
  simp only [relEq, relZero, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hy, heq⟩
    refine ⟨hx, hy, fun i => ?_⟩
    rw [heq]
    exact (hd i).dist_self (ϕ.func y)
  · rintro ⟨hx, hy, hzero⟩
    refine ⟨hx, hy, ?_⟩
    exact hsep (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩ hzero

/-- `CH03-P08-03`：命题 3.7（像集局部分离下的点值—商判据一致性）— 仅假设规范族分别在两个实际像集 `ϕ_A(U)` 与 `ϕ_B(U)` 上分离，即有两关系集相等，且单向与双向点值变换判据分别同单向与双向商变换判据等价。 -/
theorem prop_3_7_separating_images_bridge {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hdom : U ⊆ dom ϕA ∩ dom ϕB)
    (hsepA : IsSeparatingOn d (operator_image ϕA U))
    (hsepB : IsSeparatingOn d (operator_image ϕB U)) :
    relEq ϕA U = relZero d ϕA U ∧
    relEq ϕB U = relZero d ϕB U ∧
    ((∃ T : operator_image ϕA U → X, FactorsThroughImage ϕA ϕB U T) ↔
      (∃ Tbar : ImageZeroQuotient d hd ϕA U → ImageZeroQuotient d hd ϕB U,
        QuotientFactorsThroughImage d hd ϕA ϕB U Tbar)) ∧
    (((∃ TAB : operator_image ϕA U → X, FactorsThroughImage ϕA ϕB U TAB) ∧
      (∃ TBA : operator_image ϕB U → X, FactorsThroughImage ϕB ϕA U TBA)) ↔
      ((∃ TAB : ImageZeroQuotient d hd ϕA U → ImageZeroQuotient d hd ϕB U,
          QuotientFactorsThroughImage d hd ϕA ϕB U TAB) ∧
        (∃ TBA : ImageZeroQuotient d hd ϕB U → ImageZeroQuotient d hd ϕA U,
          QuotientFactorsThroughImage d hd ϕB ϕA U TBA))) := by
  have heqA := relEq_eq_relZero_of_separatingOn_image d hd ϕA U hsepA
  have heqB := relEq_eq_relZero_of_separatingOn_image d hd ϕB U hsepB
  refine ⟨heqA, heqB, ?_, ?_⟩
  · rw [prop_3_6_pointwise_factorization_iff ϕA ϕB U hdom,
      prop_3_7_quotient_factorization_iff d hd ϕA ϕB U hdom, heqA, heqB]
  · rw [prop_3_6_bidirectional_iff ϕA ϕB U hdom,
      prop_3_7_bidirectional_quotient_iff d hd ϕA ϕB U hdom, heqA, heqB]

/-! ## 注：纤维包含的传递 (`CH03-P09-01` – `CH03-P09-03`) -/

/-- `CH03-P09-01`：固定公共评估域 `U` 上的纤维预序 `⪰_{fiber, U}` 具有自反性与传递性。 -/
theorem remark_fiberGe_refl_and_trans {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X) :
    (∀ ϕ : Operator X bot, U ⊆ dom ϕ → FiberGe d U ϕ ϕ) ∧
    (∀ ϕA ϕB ϕC : Operator X bot,
      U ⊆ dom ϕA → U ⊆ dom ϕB → U ⊆ dom ϕC →
      FiberGe d U ϕA ϕB → FiberGe d U ϕB ϕC → FiberGe d U ϕA ϕC) := by
  refine ⟨?_, ?_⟩
  · intro _ _
    exact Set.Subset.rfl
  · intro _ _ _ _ _ _ hAB hBC
    exact Set.Subset.trans hAB hBC

/-- 有限链上任意两层 `a ≤ b ≤ m` 的零测距关系包含辅助引理。 -/
theorem remark_fiberGe_chain_le {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X)
    (ϕ : ℕ → Operator X bot) (m : ℕ)
    (hdom : ∀ k ≤ m, U ⊆ dom (ϕ k))
    (hstep : ∀ r : ℕ, 1 ≤ r → r ≤ m → FiberGe d U (ϕ (r - 1)) (ϕ r)) :
    ∀ a b : ℕ, a ≤ b → b ≤ m → FiberGe d U (ϕ a) (ϕ b) := by
  have _ := hdom
  intro a b hab hbm
  induction b with
  | zero =>
      have ha0 : a = 0 := Nat.le_zero.mp hab
      subst ha0
      exact Set.Subset.rfl
  | succ k ih =>
      rcases Nat.of_le_succ hab with hak | rfl
      · have h₁ : FiberGe d U (ϕ a) (ϕ k) := ih hak (Nat.le_of_succ_le hbm)
        have h₂ : FiberGe d U (ϕ k) (ϕ (k + 1)) := by
          simpa using hstep (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) hbm
        exact Set.Subset.trans h₁ h₂
      · exact Set.Subset.rfl

/-- `CH03-P09-02`：若 `ϕ_0, …, ϕ_m` 具有公共评估域 `U` 且逐步满足 `ϕ_{r-1} ⪰_{fiber, U} ϕ_r`，则任意 `0 ≤ a < b ≤ m` 满足 `ϕ_a ⪰_{fiber, U} ϕ_b`。 -/
theorem remark_fiberGe_chain_lt {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X)
    (ϕ : ℕ → Operator X bot) (m : ℕ)
    (hdom : ∀ k ≤ m, U ⊆ dom (ϕ k))
    (hstep : ∀ r : ℕ, 1 ≤ r → r ≤ m → FiberGe d U (ϕ (r - 1)) (ϕ r)) :
    ∀ a b : ℕ, a < b → b ≤ m → FiberGe d U (ϕ a) (ϕ b) := by
  intro a b hab hbm
  exact remark_fiberGe_chain_le d U ϕ m hdom hstep a b (Nat.le_of_lt hab) hbm

/-- `CH03-P09-03`：若链中某一步 `1 ≤ r ≤ m` 为真包含 `R_∼(ϕ_{r-1} | U) ⊂ R_∼(ϕ_r | U)`，则差集包含于首尾差集、存在显式见证点对，且首尾为严格包含 `R_∼(ϕ_0 | U) ⊂ R_∼(ϕ_m | U)`。 -/
theorem remark_fiberGe_chain_strict {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (U : Set X)
    (ϕ : ℕ → Operator X bot) (m r : ℕ)
    (hdom : ∀ k ≤ m, U ⊆ dom (ϕ k))
    (hstep : ∀ s : ℕ, 1 ≤ s → s ≤ m → FiberGe d U (ϕ (s - 1)) (ϕ s))
    (hr1 : 1 ≤ r) (hrm : r ≤ m)
    (hstrict : relZero d (ϕ (r - 1)) U ⊂ relZero d (ϕ r) U) :
    relZero d (ϕ r) U \ relZero d (ϕ (r - 1)) U ⊆
      relZero d (ϕ m) U \ relZero d (ϕ 0) U ∧
    (∃ p : X × X,
      p ∈ relZero d (ϕ r) U \ relZero d (ϕ (r - 1)) U ∧
      p ∈ relZero d (ϕ m) U \ relZero d (ϕ 0) U) ∧
    relZero d (ϕ 0) U ⊂ relZero d (ϕ m) U := by
  have _ := hr1
  have h0_le : FiberGe d U (ϕ 0) (ϕ (r - 1)) :=
    remark_fiberGe_chain_le d U ϕ m hdom hstep 0 (r - 1) (Nat.zero_le _) (Nat.le_trans (Nat.sub_le r 1) hrm)
  have hr_le : FiberGe d U (ϕ r) (ϕ m) :=
    remark_fiberGe_chain_le d U ϕ m hdom hstep r m hrm le_rfl
  have h0m_le : FiberGe d U (ϕ 0) (ϕ m) :=
    remark_fiberGe_chain_le d U ϕ m hdom hstep 0 m (Nat.zero_le _) le_rfl
  have hdiff_sub :
      relZero d (ϕ r) U \ relZero d (ϕ (r - 1)) U ⊆
        relZero d (ϕ m) U \ relZero d (ϕ 0) U := by
    rintro p ⟨hpr, hpnot⟩
    exact ⟨hr_le hpr, fun hp0 => hpnot (h0_le hp0)⟩
  obtain ⟨p, hpr, hpnot⟩ := Set.exists_of_ssubset hstrict
  have hp_diff : p ∈ relZero d (ϕ r) U \ relZero d (ϕ (r - 1)) U := ⟨hpr, hpnot⟩
  have hp_end : p ∈ relZero d (ϕ m) U \ relZero d (ϕ 0) U := hdiff_sub hp_diff
  refine ⟨hdiff_sub, ⟨p, hp_diff, hp_end⟩, ?_⟩
  exact ⟨h0m_le, fun hrev => hp_end.2 (hrev hp_end.1)⟩

end Ch03
