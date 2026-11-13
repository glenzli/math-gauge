import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import Ch03.Partition
import Mathlib.Tactic

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

section ComputationFibers

variable {X I : Type} {bot : X}

/-- **定义（计算纤维）**：子集 `U` 内在子族复合伪度量 `d_J` 下输出与 `y` 零距的点集。 -/
def compFiber (d : I → X → X → ENNReal) (ϕ : Operator X bot) (J : Set I)
    (y : X) (U : Set X) : Set X :=
  { x ∈ U | subfamily_pseudometric d J (ϕ.func x) y = 0 }

/-- 全域计算纤维（`U = dom ϕ`）。 -/
def compFiber_global (d : I → X → X → ENNReal) (ϕ : Operator X bot) (J : Set I)
    (y : X) : Set X :=
  compFiber d ϕ J y (dom ϕ)

/-- 单分量计算纤维（`J = {j}`）。 -/
def compFiber_single (d : I → X → X → ENNReal) (ϕ : Operator X bot) (j : I)
    (y : X) (U : Set X) : Set X :=
  compFiber d ϕ {j} y U

lemma compFiber_single_eq (d : I → X → X → ENNReal) (ϕ : Operator X bot) (j : I)
    (y : X) (U : Set X) :
    compFiber_single d ϕ j y U = { x ∈ U | d j (ϕ.func x) y = 0 } := by
  ext x
  simp [compFiber_single, compFiber, subfamily_pseudometric_singleton]

lemma subfamily_pseudometric_eq_zero_iff (d : I → X → X → ENNReal) (J : Set I)
    (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  unfold subfamily_pseudometric
  constructor
  · intro h j hj
    exact le_antisymm
      (le_trans (le_iSup (fun k : {k // k ∈ J} => d k.1 x y) ⟨j, hj⟩) h.le)
      (zero_le _)
  · intro h
    exact le_antisymm (iSup_le fun j => (h j.1 j.2).le) (zero_le _)

lemma subfamily_pseudometric_symm_on (d : I → X → X → ENNReal) (J : Set I)
    (hd : ∀ j ∈ J, ExtendedPseudoMetric X bot (d j)) (x y : X) :
    subfamily_pseudometric d J x y = subfamily_pseudometric d J y x := by
  unfold subfamily_pseudometric
  congr with j
  exact (hd j.1 j.2).symm x y

lemma subfamily_pseudometric_triangle_on (d : I → X → X → ENNReal) (J : Set I)
    (hd : ∀ j ∈ J, ExtendedPseudoMetric X bot (d j)) (x y z : X) :
    subfamily_pseudometric d J x z ≤
      subfamily_pseudometric d J x y + subfamily_pseudometric d J y z := by
  unfold subfamily_pseudometric
  apply iSup_le
  intro j
  exact ((hd j.1 j.2).triangle x y z).trans <|
    add_le_add
      (le_iSup (fun k : {k // k ∈ J} => d k.1 x y) j)
      (le_iSup (fun k : {k // k ∈ J} => d k.1 y z) j)

/-- **命题 3.5 (i)**：目标在 `d_J` 下零距时，对应计算纤维相等。 -/
theorem prop_3_5_target_zero_invariant (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (U : Set X) (y y' : X)
    (_hJ : J.Nonempty) (hd : ∀ j ∈ J, ExtendedPseudoMetric X bot (d j))
    (hy : subfamily_pseudometric d J y y' = 0) :
    compFiber d ϕ J y U = compFiber d ϕ J y' U := by
  have hy' : subfamily_pseudometric d J y' y = 0 := by
    rw [subfamily_pseudometric_symm_on d J hd]
    exact hy
  ext x
  simp only [compFiber, Set.mem_setOf_eq]
  refine and_congr_right fun _ => ⟨fun hx => ?_, fun hx => ?_⟩
  · apply le_antisymm _ (zero_le _)
    calc
      subfamily_pseudometric d J (ϕ.func x) y'
          ≤ subfamily_pseudometric d J (ϕ.func x) y +
              subfamily_pseudometric d J y y' :=
            subfamily_pseudometric_triangle_on d J hd _ _ _
      _ = 0 := by rw [hx, hy, zero_add]
  · apply le_antisymm _ (zero_le _)
    calc
      subfamily_pseudometric d J (ϕ.func x) y
          ≤ subfamily_pseudometric d J (ϕ.func x) y' +
              subfamily_pseudometric d J y' y :=
            subfamily_pseudometric_triangle_on d J hd _ _ _
      _ = 0 := by rw [hx, hy', zero_add]

/-- **命题 3.5 (ii-a)**：每个像点目标的纤维非空，且全部像目标纤维覆盖 `U`。 -/
theorem prop_3_5_image_fibers_nonempty_cover (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (U : Set X)
    (_hJ : J.Nonempty) (hd : ∀ j ∈ J, ExtendedPseudoMetric X bot (d j)) :
    (∀ y ∈ ϕ.func '' U, (compFiber d ϕ J y U).Nonempty) ∧
    (⋃ y ∈ ϕ.func '' U, compFiber d ϕ J y U) = U := by
  constructor
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨x, hx, ?_⟩
    rw [subfamily_pseudometric_eq_zero_iff]
    intro j hj
    exact (hd j hj).dist_self _
  · ext x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨_, _, hx, _⟩
      exact hx
    · intro hx
      refine ⟨ϕ.func x, ⟨x, hx, rfl⟩, hx, ?_⟩
      rw [subfamily_pseudometric_eq_zero_iff]
      intro j hj
      exact (hd j hj).dist_self _

/-- 去重后的像目标计算纤维族。 -/
def fiberPartition (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (J : Set I) (U : Set X) : Set (Set X) :=
  { S | ∃ y ∈ ϕ.func '' U, S = compFiber d ϕ J y U }

/-- **命题 3.5 (ii-b)**：像目标纤维要么相等要么不交；去重后构成 `U` 的分划。 -/
theorem prop_3_5_image_fibers_partition (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (U : Set X)
    (hJ : J.Nonempty) (hd : ∀ j ∈ J, ExtendedPseudoMetric X bot (d j)) :
    (∀ y₁ ∈ ϕ.func '' U, ∀ y₂ ∈ ϕ.func '' U,
      compFiber d ϕ J y₁ U = compFiber d ϕ J y₂ U ∨
      Disjoint (compFiber d ϕ J y₁ U) (compFiber d ϕ J y₂ U)) ∧
    ∅ ∉ fiberPartition d ϕ J U ∧
    ⋃₀ fiberPartition d ϕ J U = U ∧
    (fiberPartition d ϕ J U).PairwiseDisjoint id := by
  have hdich : ∀ y₁ ∈ ϕ.func '' U, ∀ y₂ ∈ ϕ.func '' U,
      compFiber d ϕ J y₁ U = compFiber d ϕ J y₂ U ∨
      Disjoint (compFiber d ϕ J y₁ U) (compFiber d ϕ J y₂ U) := by
    intro y₁ _ y₂ _
    by_cases hdisj : Disjoint (compFiber d ϕ J y₁ U) (compFiber d ϕ J y₂ U)
    · exact Or.inr hdisj
    · left
      rw [Set.not_disjoint_iff] at hdisj
      rcases hdisj with ⟨x, hx1, hx2⟩
      have h1 : subfamily_pseudometric d J y₁ (ϕ.func x) = 0 := by
        rw [subfamily_pseudometric_symm_on d J hd]
        exact hx1.2
      have hy12 : subfamily_pseudometric d J y₁ y₂ = 0 := by
        apply le_antisymm _ (zero_le _)
        calc
          subfamily_pseudometric d J y₁ y₂
              ≤ subfamily_pseudometric d J y₁ (ϕ.func x) +
                  subfamily_pseudometric d J (ϕ.func x) y₂ :=
                subfamily_pseudometric_triangle_on d J hd _ _ _
          _ = 0 := by rw [h1, hx2.2, zero_add]
      exact prop_3_5_target_zero_invariant d ϕ J U y₁ y₂ hJ hd hy12
  refine ⟨hdich, ?_, ?_, ?_⟩
  · rintro ⟨y, hy, hbot⟩
    obtain ⟨x, hx⟩ := (prop_3_5_image_fibers_nonempty_cover d ϕ J U hJ hd).1 y hy
    rw [← hbot] at hx
    exact hx
  · ext x
    simp only [Set.mem_sUnion, fiberPartition, Set.mem_setOf_eq]
    constructor
    · rintro ⟨S, ⟨y, _, rfl⟩, hx⟩
      exact hx.1
    · intro hx
      have hcov := (prop_3_5_image_fibers_nonempty_cover d ϕ J U hJ hd).2
      have hx' : x ∈ ⋃ y ∈ ϕ.func '' U, compFiber d ϕ J y U := by
        rw [hcov]
        exact hx
      simp only [Set.mem_iUnion, exists_prop] at hx'
      rcases hx' with ⟨y, hy, hmem⟩
      exact ⟨compFiber d ϕ J y U, ⟨y, hy, rfl⟩, hmem⟩
  · rintro S₁ ⟨y₁, hy₁, rfl⟩ S₂ ⟨y₂, hy₂, rfl⟩ hne
    rcases hdich y₁ hy₁ y₂ hy₂ with heq | hdisj
    · exact False.elim (hne heq)
    · exact hdisj

/-- **命题 3.5 (iii)**：子族计算纤维等于各分量纤维之交。 -/
theorem prop_3_5_iInter_components (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (y : X) (U : Set X)
    (hJ : J.Nonempty) :
    compFiber d ϕ J y U = ⋂ j ∈ J, compFiber_single d ϕ j y U := by
  ext x
  simp only [compFiber, compFiber_single_eq, Set.mem_setOf_eq, Set.mem_iInter,
    subfamily_pseudometric_eq_zero_iff]
  constructor
  · intro ⟨hxU, hfor⟩ j hj
    exact ⟨hxU, hfor j hj⟩
  · intro hfor
    rcases hJ with ⟨j₀, hj₀⟩
    exact ⟨(hfor j₀ hj₀).1, fun j hj => (hfor j hj).2⟩

/-- **命题 3.5 (iv)**：子族扩大时计算纤维反单调缩小。 -/
theorem prop_3_5_antitone_subfamily (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J K : Set I) (y : X) (U : Set X)
    (_hJ : J.Nonempty) (hJK : J ⊆ K) :
    compFiber d ϕ K y U ⊆ compFiber d ϕ J y U := by
  intro x ⟨hxU, hK⟩
  refine ⟨hxU, ?_⟩
  rw [subfamily_pseudometric_eq_zero_iff] at hK ⊢
  intro j hj
  exact hK j (hJK hj)

/-- **命题 3.5 (v)**：单分量与全子族纤维边界。 -/
theorem prop_3_5_subfamily_boundary (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i : I) (y : X) (U : Set X) :
    (compFiber d ϕ {i} y U = compFiber_single d ϕ i y U ∧
     compFiber_single d ϕ i y U = { x ∈ U | d i (ϕ.func x) y = 0 }) ∧
    compFiber d ϕ Set.univ y U ⊆ compFiber_single d ϕ i y U := by
  refine ⟨⟨rfl, compFiber_single_eq d ϕ i y U⟩, ?_⟩
  exact prop_3_5_antitone_subfamily d ϕ {i} Set.univ y U ⟨i, Set.mem_singleton i⟩
    (Set.subset_univ _)

/-- **命题 3.5 (vi-a)**：恒等分量的计算纤维等于输入零距类。 -/
theorem prop_3_5_id_component (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (j : I) (y : X) (U : Set X)
    (hd : ExtendedPseudoMetric X bot (d j))
    (_hU : U ⊆ dom ϕ) (hj : j ∈ I_id d ϕ U) :
    compFiber_single d ϕ j y U = { x ∈ U | d j x y = 0 } := by
  rw [compFiber_single_eq]
  ext x
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun hxU => ?_
  have hfx : d j (ϕ.func x) x = 0 := hj.2 x hxU
  have hxf : d j x (ϕ.func x) = 0 := by rw [hd.symm]; exact hfx
  constructor
  · intro h
    apply le_antisymm _ (zero_le _)
    calc
      d j x y ≤ d j x (ϕ.func x) + d j (ϕ.func x) y := hd.triangle _ _ _
      _ = 0 := by rw [hxf, h, zero_add]
  · intro h
    apply le_antisymm _ (zero_le _)
    calc
      d j (ϕ.func x) y ≤ d j (ϕ.func x) x + d j x y := hd.triangle _ _ _
      _ = 0 := by rw [hfx, h, zero_add]

/-- **命题 3.5 (vi-b)**：常值分量在像目标上纤维为 `U`，正距离目标上纤维为空。 -/
theorem prop_3_5_const_component (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (j : I) (U : Set X)
    (hd : ExtendedPseudoMetric X bot (d j))
    (_hU : U ⊆ dom ϕ) (hj : j ∈ I_const d ϕ U) :
    ∀ y₀ ∈ ϕ.func '' U,
      compFiber_single d ϕ j y₀ U = U ∧
      ∀ y : X, 0 < d j y y₀ → compFiber_single d ϕ j y U = ∅ := by
  rintro y₀ ⟨x₀, hx₀, rfl⟩
  constructor
  · rw [compFiber_single_eq]
    ext x
    simp only [Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro hx
    exact hj x hx x₀ hx₀
  · intro y hy
    rw [compFiber_single_eq]
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hx hzero
    have h1 : d j (ϕ.func x) (ϕ.func x₀) = 0 := hj x hx x₀ hx₀
    have h2 : d j y (ϕ.func x) = 0 := by rw [hd.symm]; exact hzero
    have hle : d j y (ϕ.func x₀) ≤ 0 := by
      calc
        d j y (ϕ.func x₀) ≤ d j y (ϕ.func x) + d j (ϕ.func x) (ϕ.func x₀) :=
          hd.triangle _ _ _
        _ = 0 := by rw [h2, h1, zero_add]
    exact ne_of_gt hy (le_antisymm hle (zero_le _))

end ComputationFibers

section FactorizationAndQuotients

variable {X I : Type} {bot : X}

/-- 点值相等关系 `R_=(ϕ | U)`。 -/
def eqRel (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  { p | p.1 ∈ U ∧ p.2 ∈ U ∧ ϕ.func p.1 = ϕ.func p.2 }

/-- 全分量零距关系 `R_~(ϕ | U)`。 -/
def zeroRel (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  { p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (ϕ.func p.1) (ϕ.func p.2) }

lemma zeroRel_iff_mem_compFiber [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) :
    ∀ x ∈ U, ∀ y ∈ U,
      (x, y) ∈ zeroRel d ϕ U ↔ y ∈ compFiber d ϕ Set.univ (ϕ.func x) U := by
  intro x hx y hy
  simp only [zeroRel, compFiber, Set.mem_setOf_eq, subfamily_pseudometric_eq_zero_iff,
    Set.mem_univ, true_implies]
  constructor
  · rintro ⟨_, _, hrel⟩
    refine ⟨hy, fun i => ?_⟩
    rw [(hd i).symm]
    exact hrel i
  · rintro ⟨_, hfib⟩
    refine ⟨hx, hy, fun i => ?_⟩
    rw [(hd i).symm]
    exact hfib i

/-- 规范族在子集 `S` 上分离。 -/
def IsSeparatingOn (d : I → X → X → ENNReal) (S : Set X) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, GaugeZeroRelated d x y → x = y

/-- 像集 `ϕ(U)` 上的族零距等价关系 `Setoid`。 -/
def imageZeroSetoid (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) :
    Setoid { z : X // z ∈ ϕ.func '' U } where
  r z₁ z₂ := GaugeZeroRelated d z₁.1 z₂.1
  iseqv := by
    have heq := gauge_zero_related_equivalence d
      (fun i => (hd i).dist_self) (fun i => (hd i).symm) (fun i => (hd i).triangle)
    exact ⟨fun z => heq.refl z.1, fun h => heq.symm h, fun h1 h2 => heq.trans h1 h2⟩

/-- 像商空间 `ϕ(U) / ~_G`。 -/
def ImageQuotient (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) : Type :=
  Quotient (imageZeroSetoid d ϕ U hd)

/-- 零测距纤维预序 `ϕA ⪰_{fiber, U} ϕB`。 -/
def FiberPreorder (d : I → X → X → ENNReal) (U : Set X)
    (ϕA ϕB : Operator X bot) : Prop :=
  zeroRel d ϕA U ⊆ zeroRel d ϕB U

/-- **命题 3.6 (i-必要)**：点值像映射存在蕴含相等关系包含。 -/
theorem prop_3_6_factor_necessary (ϕA ϕB : Operator X bot) (U : Set X)
    (_hU : U ⊆ dom ϕA ∩ dom ϕB)
    (hex : ∃ T : { z : X // z ∈ ϕA.func '' U } → X,
      ∀ (x : X) (hx : x ∈ U),
        T ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩ = ϕB.func x) :
    eqRel ϕA U ⊆ eqRel ϕB U := by
  rcases hex with ⟨T, hT⟩
  rintro ⟨x, y⟩ ⟨hx, hy, heq⟩
  refine ⟨hx, hy, ?_⟩
  have h1 := hT x hx
  have h2 := hT y hy
  rw [← h1, ← h2]
  congr 2

/-- **命题 3.6 (i-充分)**：相等关系包含时构造良定义像映射并验证 `T ∘ ϕA = ϕB`（含 `U = ∅`）。 -/
theorem prop_3_6_factor_sufficient (ϕA ϕB : Operator X bot) (U : Set X)
    (_hU : U ⊆ dom ϕA ∩ dom ϕB)
    (hsub : eqRel ϕA U ⊆ eqRel ϕB U) :
    ∃ T : { z : X // z ∈ ϕA.func '' U } → X,
      ∀ (x : X) (hx : x ∈ U),
        T ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩ = ϕB.func x := by
  classical
  refine ⟨fun z => ϕB.func (Classical.choose z.2), ?_⟩
  intro x hx
  let z : { z : X // z ∈ ϕA.func '' U } := ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩
  have hspec := Classical.choose_spec z.2
  have hmem : (Classical.choose z.2, x) ∈ eqRel ϕA U :=
    ⟨hspec.1, hx, hspec.2⟩
  exact (hsub hmem).2.2

/-- **命题 3.6 (i)**：点值像值因子化存在当且仅当相等关系包含。 -/
theorem prop_3_6_factor_iff (ϕA ϕB : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕA ∩ dom ϕB) :
    (∃ T : { z : X // z ∈ ϕA.func '' U } → X,
      ∀ (x : X) (hx : x ∈ U),
        T ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩ = ϕB.func x) ↔
    eqRel ϕA U ⊆ eqRel ϕB U :=
  ⟨prop_3_6_factor_necessary ϕA ϕB U hU, prop_3_6_factor_sufficient ϕA ϕB U hU⟩

/-- **命题 3.6 (ii)**：双向点值像值变换存在当且仅当相等关系相等。 -/
theorem prop_3_6_mutual_factor_iff (ϕA ϕB : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕA ∩ dom ϕB) :
    ((∃ T₁ : { z : X // z ∈ ϕA.func '' U } → X,
        ∀ (x : X) (hx : x ∈ U),
          T₁ ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩ = ϕB.func x) ∧
     (∃ T₂ : { z : X // z ∈ ϕB.func '' U } → X,
        ∀ (x : X) (hx : x ∈ U),
          T₂ ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩ = ϕA.func x)) ↔
    eqRel ϕA U = eqRel ϕB U := by
  have hU' : U ⊆ dom ϕB ∩ dom ϕA := by
    rw [Set.inter_comm]
    exact hU
  rw [prop_3_6_factor_iff ϕA ϕB U hU, prop_3_6_factor_iff ϕB ϕA U hU', Set.Subset.antisymm_iff]

/-- **命题 3.6 (iii)**：单分量情形下，由 `ϕA` 的 `K_A`-co-Lip 下界与 `ϕB` 的 `L_B`-Lip 上界推出 `T` 的 `L_B / K_A` 标量 Lip 界。 -/
theorem prop_3_6_factor_lip_bound (d : X → X → ENNReal)
    (ϕA ϕB : Operator X bot) (U : Set X)
    (_hU : U ⊆ dom ϕA ∩ dom ϕB)
    (T : { z : X // z ∈ ϕA.func '' U } → X)
    (hT : ∀ (x : X) (hx : x ∈ U),
      T ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩ = ϕB.func x)
    (K_A L_B : ENNReal) (hKpos : 0 < K_A) (hKfin : K_A < ⊤) (_hLfin : L_B < ⊤)
    (hcoLip : ∀ x ∈ U, ∀ x' ∈ U, K_A * d x x' ≤ d (ϕA.func x) (ϕA.func x'))
    (hLip : ∀ x ∈ U, ∀ x' ∈ U, d (ϕB.func x) (ϕB.func x') ≤ L_B * d x x') :
    ∀ y y' : { z : X // z ∈ ϕA.func '' U },
      d (T y) (T y') ≤ (L_B / K_A) * d y.1 y'.1 := by
  intro y y'
  rcases y with ⟨yval, ⟨x, hx, rfl⟩⟩
  rcases y' with ⟨y'val, ⟨x', hx', rfl⟩⟩
  rw [hT x hx, hT x' hx']
  have hK_ne_zero : K_A ≠ 0 := ne_of_gt hKpos
  have hK_ne_top : K_A ≠ ⊤ := ne_of_lt hKfin
  have hd_le : d x x' ≤ K_A⁻¹ * d (ϕA.func x) (ϕA.func x') := by
    calc
      d x x' = K_A⁻¹ * (K_A * d x x') := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hK_ne_zero hK_ne_top, one_mul]
      _ ≤ K_A⁻¹ * d (ϕA.func x) (ϕA.func x') :=
        mul_le_mul_right (hcoLip x hx x' hx') K_A⁻¹
  calc
    d (ϕB.func x) (ϕB.func x') ≤ L_B * d x x' := hLip x hx x' hx'
    _ ≤ L_B * (K_A⁻¹ * d (ϕA.func x) (ϕA.func x')) := mul_le_mul_right hd_le L_B
    _ = (L_B / K_A) * d (ϕA.func x) (ϕA.func x') := by
        rw [div_eq_mul_inv, mul_assoc]

/-- 命题 3.6 (iii) 与第 2 章 `IsCoLipMatrix`/`IsLipMatrix`（`[Subsingleton I]` 单分量情形）的接口桥接。 -/
theorem prop_3_6_factor_lip_bound_matrix [Fintype I] [Subsingleton I]
    (d : I → X → X → ENNReal) (i : I)
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hU : U ⊆ dom ϕA ∩ dom ϕB)
    (T : { z : X // z ∈ ϕA.func '' U } → X)
    (hT : ∀ (x : X) (hx : x ∈ U),
      T ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩ = ϕB.func x)
    (K_A L_B : I → I → ENNReal)
    (hK : IsCoLipMatrix d ϕA U K_A) (hL : IsLipMatrix d ϕB U L_B)
    (hKpos : 0 < K_A i i) (hKfin : K_A i i < ⊤) (hLfin : L_B i i < ⊤) :
    ∀ y y' : { z : X // z ∈ ϕA.func '' U },
      d i (T y) (T y') ≤ (L_B i i / K_A i i) * d i y.1 y'.1 := by
  apply prop_3_6_factor_lip_bound (d i) ϕA ϕB U hU T hT (K_A i i) (L_B i i) hKpos hKfin hLfin
  · intro x hx x' hx'
    have h := hK.2.2 x hx x' hx' i
    have hsum : (∑ k : I, K_A k i * d k x x') = K_A i i * d i x x' := by
      apply Finset.sum_eq_single i
      · intro k _ hk
        exact (hk (Subsingleton.elim k i)).elim
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    rw [hsum] at h
    exact h
  · exact single_component_lip_matrix_ineq d ϕB U L_B i hL

/-- **命题 3.7（单向商映射存在判据）**：商映射存在且满足规定赋值公式，当且仅当零距关系包含。 -/
theorem prop_3_7_quotient_factor_iff (d : I → X → X → ENNReal)
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom ϕA ∩ dom ϕB) :
    (∃ Tbar : ImageQuotient d ϕA U hd → ImageQuotient d ϕB U hd,
      ∀ (x : X) (hx : x ∈ U),
        Tbar (Quotient.mk (imageZeroSetoid d ϕA U hd)
          ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩) =
        Quotient.mk (imageZeroSetoid d ϕB U hd)
          ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩) ↔
    zeroRel d ϕA U ⊆ zeroRel d ϕB U := by
  classical
  constructor
  · rintro ⟨Tbar, hTbar⟩ ⟨x, y⟩ ⟨hx, hy, hrel⟩
    refine ⟨hx, hy, ?_⟩
    have hq :
        Quotient.mk (imageZeroSetoid d ϕA U hd)
          ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩ =
        Quotient.mk (imageZeroSetoid d ϕA U hd)
          ⟨ϕA.func y, Set.mem_image_of_mem _ hy⟩ :=
      Quotient.sound hrel
    have hqB :
        Quotient.mk (imageZeroSetoid d ϕB U hd)
          ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩ =
        Quotient.mk (imageZeroSetoid d ϕB U hd)
          ⟨ϕB.func y, Set.mem_image_of_mem _ hy⟩ := by
      rw [← hTbar x hx, ← hTbar y hy, hq]
    exact Quotient.exact hqB
  · intro hsub
    let f : { z : X // z ∈ ϕA.func '' U } → ImageQuotient d ϕB U hd := fun z =>
      Quotient.mk (imageZeroSetoid d ϕB U hd)
        ⟨ϕB.func (Classical.choose z.2),
          Set.mem_image_of_mem _ (Classical.choose_spec z.2).1⟩
    have hf_resp : ∀ z₁ z₂ : { z : X // z ∈ ϕA.func '' U },
        (imageZeroSetoid d ϕA U hd).r z₁ z₂ → f z₁ = f z₂ := by
      intro z₁ z₂ hrel
      apply Quotient.sound
      have hs1 := Classical.choose_spec z₁.2
      have hs2 := Classical.choose_spec z₂.2
      have hA : (Classical.choose z₁.2, Classical.choose z₂.2) ∈ zeroRel d ϕA U := by
        refine ⟨hs1.1, hs2.1, fun i => ?_⟩
        rw [hs1.2, hs2.2]
        exact hrel i
      exact (hsub hA).2.2
    refine ⟨Quotient.lift f hf_resp, ?_⟩
    intro x hx
    change f ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩ = _
    apply Quotient.sound
    have hs := Classical.choose_spec (Set.mem_image_of_mem ϕA.func hx)
    have hA : (Classical.choose (Set.mem_image_of_mem ϕA.func hx), x) ∈ zeroRel d ϕA U := by
      refine ⟨hs.1, hx, fun i => ?_⟩
      rw [hs.2]
      exact (hd i).dist_self _
    exact (hsub hA).2.2

/-- **命题 3.7（双向商映射存在判据）**：双向商映射存在当且仅当零距关系相等。 -/
theorem prop_3_7_quotient_mutual_iff (d : I → X → X → ENNReal)
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom ϕA ∩ dom ϕB) :
    ((∃ Tbar₁ : ImageQuotient d ϕA U hd → ImageQuotient d ϕB U hd,
        ∀ (x : X) (hx : x ∈ U),
          Tbar₁ (Quotient.mk (imageZeroSetoid d ϕA U hd)
            ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩) =
          Quotient.mk (imageZeroSetoid d ϕB U hd)
            ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩) ∧
     (∃ Tbar₂ : ImageQuotient d ϕB U hd → ImageQuotient d ϕA U hd,
        ∀ (x : X) (hx : x ∈ U),
          Tbar₂ (Quotient.mk (imageZeroSetoid d ϕB U hd)
            ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩) =
          Quotient.mk (imageZeroSetoid d ϕA U hd)
            ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩)) ↔
    zeroRel d ϕA U = zeroRel d ϕB U := by
  have hU' : U ⊆ dom ϕB ∩ dom ϕA := by
    rw [Set.inter_comm]
    exact hU
  rw [prop_3_7_quotient_factor_iff d ϕA ϕB U hd hU,
      prop_3_7_quotient_factor_iff d ϕB ϕA U hd hU',
      Set.Subset.antisymm_iff]

/-- **命题 3.7（像集各自分离时点值判据与商值判据等价）**。 -/
theorem prop_3_7_separating_images_equiv (d : I → X → X → ENNReal)
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom ϕA ∩ dom ϕB)
    (hsepA : IsSeparatingOn d (ϕA.func '' U))
    (hsepB : IsSeparatingOn d (ϕB.func '' U)) :
    (eqRel ϕA U = zeroRel d ϕA U ∧ eqRel ϕB U = zeroRel d ϕB U) ∧
    ((∃ T : { z : X // z ∈ ϕA.func '' U } → X,
        ∀ (x : X) (hx : x ∈ U),
          T ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩ = ϕB.func x) ↔
     (∃ Tbar : ImageQuotient d ϕA U hd → ImageQuotient d ϕB U hd,
        ∀ (x : X) (hx : x ∈ U),
          Tbar (Quotient.mk (imageZeroSetoid d ϕA U hd)
            ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩) =
          Quotient.mk (imageZeroSetoid d ϕB U hd)
            ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩)) ∧
    (((∃ T₁ : { z : X // z ∈ ϕA.func '' U } → X,
        ∀ (x : X) (hx : x ∈ U),
          T₁ ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩ = ϕB.func x) ∧
      (∃ T₂ : { z : X // z ∈ ϕB.func '' U } → X,
        ∀ (x : X) (hx : x ∈ U),
          T₂ ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩ = ϕA.func x)) ↔
     ((∃ Tbar₁ : ImageQuotient d ϕA U hd → ImageQuotient d ϕB U hd,
        ∀ (x : X) (hx : x ∈ U),
          Tbar₁ (Quotient.mk (imageZeroSetoid d ϕA U hd)
            ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩) =
          Quotient.mk (imageZeroSetoid d ϕB U hd)
            ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩) ∧
      (∃ Tbar₂ : ImageQuotient d ϕB U hd → ImageQuotient d ϕA U hd,
        ∀ (x : X) (hx : x ∈ U),
          Tbar₂ (Quotient.mk (imageZeroSetoid d ϕB U hd)
            ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩) =
          Quotient.mk (imageZeroSetoid d ϕA U hd)
            ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩))) := by
  have heqA : eqRel ϕA U = zeroRel d ϕA U := by
    ext ⟨x, y⟩
    simp only [eqRel, zeroRel, Set.mem_setOf_eq]
    refine and_congr_right fun hx => and_congr_right fun hy => ⟨?_, ?_⟩
    · intro h i
      rw [h]
      exact (hd i).dist_self _
    · intro h
      exact hsepA _ (Set.mem_image_of_mem _ hx) _ (Set.mem_image_of_mem _ hy) h
  have heqB : eqRel ϕB U = zeroRel d ϕB U := by
    ext ⟨x, y⟩
    simp only [eqRel, zeroRel, Set.mem_setOf_eq]
    refine and_congr_right fun hx => and_congr_right fun hy => ⟨?_, ?_⟩
    · intro h i
      rw [h]
      exact (hd i).dist_self _
    · intro h
      exact hsepB _ (Set.mem_image_of_mem _ hx) _ (Set.mem_image_of_mem _ hy) h
  refine ⟨⟨heqA, heqB⟩, ?_, ?_⟩
  · rw [prop_3_6_factor_iff ϕA ϕB U hU, prop_3_7_quotient_factor_iff d ϕA ϕB U hd hU,
        heqA, heqB]
  · rw [prop_3_6_mutual_factor_iff ϕA ϕB U hU,
        prop_3_7_quotient_mutual_iff d ϕA ϕB U hd hU, heqA, heqB]

/-- **注（纤维预序的自反性与传递性）**。 -/
theorem remark_fiber_preorder_refl_trans (d : I → X → X → ENNReal) (U : Set X) :
    (∀ ϕ : Operator X bot, FiberPreorder d U ϕ ϕ) ∧
    (∀ ϕ₁ ϕ₂ ϕ₃ : Operator X bot,
      FiberPreorder d U ϕ₁ ϕ₂ → FiberPreorder d U ϕ₂ ϕ₃ → FiberPreorder d U ϕ₁ ϕ₃) := by
  refine ⟨fun _ => Set.Subset.rfl, fun _ _ _ h12 h23 => h12.trans h23⟩

/-- **注（有限链上纤维包含的传递）**：相邻步满足纤维预序时，任意两层均满足纤维预序。 -/
theorem remark_fiber_preorder_chain (d : I → X → X → ENNReal) (U : Set X)
    (m : ℕ) (ϕ : Fin (m + 1) → Operator X bot)
    (hstep : ∀ r : Fin m, FiberPreorder d U (ϕ r.castSucc) (ϕ r.succ)) :
    ∀ a b : Fin (m + 1), a ≤ b → FiberPreorder d U (ϕ a) (ϕ b) := by
  intro a b hab
  rcases a with ⟨a, ha⟩
  rcases b with ⟨b, hb⟩
  change a ≤ b at hab
  induction b with
  | zero =>
      have ha0 : a = 0 := Nat.eq_zero_of_le_zero hab
      subst ha0
      exact Set.Subset.rfl
  | succ b ih =>
      rcases Nat.lt_or_eq_of_le hab with hlt | heq
      · have hle : a ≤ b := Nat.lt_succ_iff.mp hlt
        have hb' : b < m + 1 := Nat.lt_of_succ_lt hb
        have hstep_b := hstep ⟨b, Nat.lt_of_succ_lt_succ hb⟩
        exact (ih hb' hle).trans hstep_b
      · subst heq
        exact Set.Subset.rfl

/-- **注（链中存在真包含时端点之间亦真包含，并给出差集见证）**。 -/
theorem remark_fiber_preorder_chain_strict (d : I → X → X → ENNReal) (U : Set X)
    (m : ℕ) (ϕ : Fin (m + 1) → Operator X bot)
    (hstep : ∀ r : Fin m, FiberPreorder d U (ϕ r.castSucc) (ϕ r.succ))
    (hstrict : ∃ r : Fin m, zeroRel d (ϕ r.castSucc) U ⊂ zeroRel d (ϕ r.succ) U) :
    zeroRel d (ϕ ⟨0, Nat.zero_lt_succ m⟩) U ⊂ zeroRel d (ϕ ⟨m, Nat.lt_succ_self m⟩) U ∧
    ∃ p : X × X, p ∈ zeroRel d (ϕ ⟨m, Nat.lt_succ_self m⟩) U \
      zeroRel d (ϕ ⟨0, Nat.zero_lt_succ m⟩) U := by
  rcases hstrict with ⟨r, hsub, hnot⟩
  have hdiff : (zeroRel d (ϕ r.succ) U \ zeroRel d (ϕ r.castSucc) U).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at hempty
    exact hnot hempty
  rcases hdiff with ⟨p, hpin, hpout⟩
  have h0r : FiberPreorder d U (ϕ ⟨0, Nat.zero_lt_succ m⟩) (ϕ r.castSucc) :=
    remark_fiber_preorder_chain d U m ϕ hstep _ _ (Nat.zero_le _)
  have hrm : FiberPreorder d U (ϕ r.succ) (ϕ ⟨m, Nat.lt_succ_self m⟩) :=
    remark_fiber_preorder_chain d U m ϕ hstep _ _ r.succ.is_le
  have h0m : FiberPreorder d U (ϕ ⟨0, Nat.zero_lt_succ m⟩) (ϕ ⟨m, Nat.lt_succ_self m⟩) :=
    remark_fiber_preorder_chain d U m ϕ hstep _ _ (Nat.zero_le _)
  have hp_in_m : p ∈ zeroRel d (ϕ ⟨m, Nat.lt_succ_self m⟩) U := hrm hpin
  have hp_notin_0 : p ∉ zeroRel d (ϕ ⟨0, Nat.zero_lt_succ m⟩) U := fun hp0 => hpout (h0r hp0)
  refine ⟨⟨h0m, fun hrev => hp_notin_0 (hrev hp_in_m)⟩, p, hp_in_m, hp_notin_0⟩

end FactorizationAndQuotients

end Ch03
