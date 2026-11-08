FULL

# MG-C003 · 第 1 轮自查后的完整交付

上一轮并未 100% 覆盖原始清单：它明确保留了 19 个 incomplete 项。本轮补齐这些项目，重新提交完整源码及完整对齐表；没有修改原始规格、冻结背景或上一轮锁定的 answer.md。

本轮新增并核查：

- 七点双分量反例的合法结构、实际像域及非封闭性。
- 吸收实线上的阶跃算子，精确合法半径区间、点态半径、固定域上的零统一半径，以及任意有限正输入尺度的两点覆盖反例。
- 实线二点/单点直径反例。
- 绝对值读数伪度量下的仿射算子、自复合纤维和分量类型。
- 平移例的完整去重纤维分划，以及精确 3/2 半径下的两端内部覆盖数和熵差。
- floor 算子在四个指定域上的直径、统一半径、阈值类型及反例。
- 四点重排例在全部正精度下的覆盖数分段和端点、内部中心限制、两算子的像集与熵差、最优 Lip 常数及 7/4 精度比较。
- 从完整 co-Lip 矩阵行到单条目标量下界的显式桥接。

alignment.json 恰好包含原清单的 92 个不同 ID，本轮均标为 complete，并逐项提供实际声明和表示说明。所有目标和数学辅助证明均在 Main.lean 中；Audit.lean 仅负责导入及审计，没有另藏的目标模块。

验证环境为 Lean 4.29.1，编译器提交 f72c35b3f637c8c6571d353742168ab66cc22c00，使用题目固定的 Mathlib 及冻结背景。Main.lean 已重新编译成功；Audit.lean 对 271 个目标、辅助及被映射的背景声明进行了声明存在性与传递公理检查，结果仅出现 propext、Classical.choice、Quot.sound。源码不含 sorry、admit、新公理或跳过内核检查的设施。少量弃用/未使用参数提示不影响编译。

表示说明：一般性命题对任意函数和相应伪度量公理证明，因此适用于原文保持吸收元的算子及其合法受限域。具体反例和习题则在 Option ℝ 或明确有限类型上构造合法 Operator 和 ExtendedPseudoMetric。所有有理数端点使用精确运算；扩展无穷值未替换为有限截断。Bool 的 true/false 分别代表阈值分类的 1/0。熵差定义要求原文的有限性析取证明。

本轮逐项核查未发现仍未完成的项目。内核检查保证所交声明及证明成立；源码到原文的语义对应仍应结合 alignment.json 阅读，不将编译成功等同于独立人工逐字语义审阅。

归属：数学内容来自 Zhe Li（Glen Li / glenzli），ORCID https://orcid.org/0009-0006-6536-3453，《The Operator Evolution Theory》，https://glenzli.com/books/oet/ ，题目所给版本 DOI https://doi.org/10.5281/zenodo.21457931，依 CC BY 4.0（https://creativecommons.org/licenses/by/4.0/）使用。本交付是对该来源的新 Lean 形式化，不主张原理论的原创性。冻结 formal_oet 源码和题目提供的 lean-local 沿用附件，不修改、不重复提交。

下面提交全部四个文件的全文。编译入口为 build.sh 或 Main.lean，公理审计入口为 Audit.lean。

```sh filename=build.sh
#!/bin/sh
set -eu
cd "$(dirname "$0")"
./lean-local -o formal_oet/vol_01/ch_01_foundations/gauge_space.olean formal_oet/vol_01/ch_01_foundations/gauge_space.lean
./lean-local -o formal_oet/vol_01/ch_01_foundations/metric_entropy.olean formal_oet/vol_01/ch_01_foundations/metric_entropy.lean
./lean-local -o formal_oet/vol_01/ch_01_foundations/operator_space.olean formal_oet/vol_01/ch_01_foundations/operator_space.lean
./lean-local -o Main.olean Main.lean
./lean-local Audit.lean
```

```lean filename=Main.lean
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib
import formal_oet.vol_01.ch_01_foundations.operator_space

/- Formalization of Chapter 3 of Zhe Li's The Operator Evolution Theory.
   All results are stated for arbitrary functions, hence apply in particular to
   absorbing-point-preserving operators on every allowed restricted domain. -/
namespace Chapter3
open Set
open formal_oet.vol_01.ch_01_foundations
variable {X I : Type}

def Const (d : X → X → ENNReal) (f : X → X) (U : Set X) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, d (f x) (f y) = 0
def Fixed (d : X → X → ENNReal) (f : X → X) (U : Set X) : Prop :=
  ∀ x ∈ U, d (f x) x = 0
def Ident (d : X → X → ENNReal) (f : X → X) (U : Set X) : Prop :=
  ¬ Const d f U ∧ Fixed d f U
def Active (d : X → X → ENNReal) (f : X → X) (U : Set X) : Prop :=
  ¬ (Const d f U ∨ Ident d f U)

theorem component_partition (d : X → X → ENNReal) (f : X → X) (U : Set X) :
    (Const d f U ∨ Ident d f U ∨ Active d f U) ∧
    ¬ (Const d f U ∧ Ident d f U) ∧
    ¬ (Const d f U ∧ Active d f U) ∧ ¬ (Ident d f U ∧ Active d f U) := by
  unfold Active Ident
  tauto

def Fiber (d : I → X → X → ENNReal) (f : X → X) (U : Set X)
    (J : Set I) (y : X) : Set X := {x | x ∈ U ∧ ∀ j ∈ J, d j (f x) y = 0}

theorem composite_zero (d : I → X → X → ENNReal) (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    apply le_antisymm _ (zero_le _)
    calc
      d j x y ≤ subfamily_pseudometric d J x y := le_iSup_of_le ⟨j,hj⟩ le_rfl
      _ = 0 := h
  · intro h
    apply le_antisymm _ (zero_le _)
    apply iSup_le
    intro j
    exact le_of_eq (h j j.property)

theorem fiber_representation (d : I → X → X → ENNReal) (f : X → X)
    (U : Set X) (J : Set I) (y : X) :
    Fiber d f U J y = {x ∈ U | subfamily_pseudometric d J (f x) y = 0} := by
  ext x
  simp [Fiber, composite_zero]

def EqRel (f : X → X) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f p.1 = f p.2}
def ZeroRel (d : I → X → X → ENNReal) (f : X → X) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ ∀ i, d i (f p.1) (f p.2) = 0}
def FiberPreorder (d : I → X → X → ENNReal) (U : Set X) (f g : X → X) : Prop :=
  ZeroRel d f U ⊆ ZeroRel d g U

theorem fiber_preorder_refl (d : I → X → X → ENNReal) (U : Set X) (f : X → X) :
    FiberPreorder d U f f := Subset.rfl

theorem fiber_preorder_trans (d : I → X → X → ENNReal) (U : Set X) (f g h : X → X)
    (hfg : FiberPreorder d U f g) (hgh : FiberPreorder d U g h) :
    FiberPreorder d U f h := hfg.trans hgh

section Metric
variable {d : X → X → ENNReal}
variable (self : ∀ x, d x x = 0) (symm : ∀ x y, d x y = d y x)
variable (tri : ∀ x y z, d x z ≤ d x y + d y z)

include tri in
theorem zero_trans {x y z : X} (hxy : d x y = 0) (hyz : d y z = 0) : d x z = 0 := by
  apply le_antisymm _ (zero_le _)
  simpa [hxy, hyz] using tri x y z

include symm tri in
theorem zero_replace {a b c : X} (hab : d a b = 0) : d a c = d b c := by
  apply le_antisymm
  · simpa [hab] using tri a b c
  · have hba : d b a = 0 := (symm b a).trans hab
    simpa [hba] using tri b a c

include symm tri in
theorem fixed_isometry {f : X → X} {U : Set X} (h : Fixed d f U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) : d (f x) (f y) = d x y := by
  rw [zero_replace symm tri (h x hx), symm x (f y),
    zero_replace symm tri (h y hy), symm y x]

include symm tri in
theorem ident_isometry {f : X → X} {U : Set X} (h : Ident d f U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) : d (f x) (f y) = d x y :=
  fixed_isometry symm tri h.2 hx hy

theorem outer_const {f g : X → X} {U : Set X} (h : Const d g (f '' U)) :
    Const d (g ∘ f) U := fun x hx y hy => h (f x) ⟨x,hx,rfl⟩ (f y) ⟨y,hy,rfl⟩

include symm tri in
theorem ident_comp {f g : X → X} {U : Set X}
    (hf : Ident d f U) (hg : Ident d g (f '' U)) : Ident d (g ∘ f) U := by
  constructor
  · intro hc
    apply hf.1
    intro x hx y hy
    rw [← ident_isometry symm tri hg ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩]
    exact hc x hx y hy
  · intro x hx
    exact zero_trans tri (hg.2 (f x) ⟨x,hx,rfl⟩) (hf.2 x hx)

include symm tri in
theorem active_comp {f g : X → X} {U : Set X} (h : Active d (g ∘ f) U) :
    Active d f U ∨ Active d g (f '' U) := by
  by_contra hn
  have hf : Const d f U ∨ Ident d f U := by unfold Active at hn; tauto
  have hg : Const d g (f '' U) ∨ Ident d g (f '' U) := by unfold Active at hn; tauto
  rcases hg with hg | hg
  · exact h (Or.inl (outer_const hg))
  rcases hf with hf | hf
  · apply h; left
    intro x hx y hy
    change d (g (f x)) (g (f y)) = 0
    rw [ident_isometry symm tri hg ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩]
    exact hf x hx y hy
  · exact h (Or.inr (ident_comp symm tri hf hg))

include self in
theorem identity_not_active (U : Set X) : ¬ Active d id U := by
  intro h
  by_cases hc : Const d id U
  · exact h (Or.inl hc)
  · exact h (Or.inr ⟨hc, fun x _ => self x⟩)
end Metric

theorem const_zero_row {d : I → X → X → ENNReal} {f : X → X} {U : Set X} {i : I}
    (h : Const (d i) f U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i (f x) (f y) ≤ ∑' k : I, (0 : ENNReal) * d k x y := by
  simp [h x hx y hy]

theorem const_colip_entry {d : I → X → X → ENNReal} {f : X → X} {U : Set X}
    {i k : I} (K : I → ENNReal) (hc : Const (d i) f U)
    (hk : ∀ x ∈ U, ∀ y ∈ U, (∑' l, K l * d l x y) ≤ d i (f x) (f y))
    (hp : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) : K k = 0 := by
  obtain ⟨x,hx,y,hy,hp⟩ := hp
  have hle : K k * d k x y ≤ 0 := by
    calc
      K k * d k x y ≤ ∑' l, K l * d l x y := ENNReal.le_tsum k
      _ ≤ d i (f x) (f y) := hk x hx y hy
      _ = 0 := hc x hx y hy
  exact (mul_eq_zero.mp (le_antisymm hle (zero_le _))).resolve_right (ne_of_gt hp)

section Fibers
variable {d : I → X → X → ENNReal} {f : X → X} {U : Set X} {J K : Set I}
variable (self : ∀ i x, d i x x = 0) (symm : ∀ i x y, d i x y = d i y x)
variable (tri : ∀ i x y z, d i x z ≤ d i x y + d i y z)

include symm tri in
theorem fiber_target_zero {y z : X} (h : ∀ i ∈ J, d i y z = 0) :
    Fiber d f U J y = Fiber d f U J z := by
  ext x
  constructor
  · rintro ⟨hx,hxy⟩
    exact ⟨hx, fun i hi => zero_trans (tri i) (hxy i hi) (h i hi)⟩
  · rintro ⟨hx,hxz⟩
    exact ⟨hx, fun i hi => zero_trans (tri i) (hxz i hi) ((symm i z y).trans (h i hi))⟩

include self in
theorem fiber_image_nonempty {y : X} (hy : y ∈ f '' U) : (Fiber d f U J y).Nonempty := by
  obtain ⟨x,hx,rfl⟩ := hy
  exact ⟨x,hx,fun i _ => self i (f x)⟩

include self in
theorem fiber_cover : (⋃ y ∈ f '' U, Fiber d f U J y) = U := by
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨y,hy,hx⟩; exact hx.1
  · intro hx
    exact ⟨f x,⟨x,hx,rfl⟩,hx,fun i _ => self i (f x)⟩

include symm tri in
theorem fibers_equal_or_disjoint (y z : X) :
    Fiber d f U J y = Fiber d f U J z ∨ Disjoint (Fiber d f U J y) (Fiber d f U J z) := by
  by_cases h : ∃ x, x ∈ Fiber d f U J y ∧ x ∈ Fiber d f U J z
  · obtain ⟨x,hxy,hxz⟩ := h
    left
    apply fiber_target_zero symm tri
    intro i hi
    exact zero_trans (tri i) ((symm i y (f x)).trans (hxy.2 i hi)) (hxz.2 i hi)
  · right
    rw [Set.disjoint_left]
    intro x hx hz
    exact h ⟨x,hx,hz⟩

theorem fiber_intersection (hJ : J.Nonempty) (y : X) :
    Fiber d f U J y = ⋂ j ∈ J, Fiber d f U {j} y := by
  ext x
  simp only [Fiber, mem_setOf_eq, mem_iInter, mem_singleton_iff]
  constructor
  · rintro ⟨hx,h⟩ j hj
    exact ⟨hx,fun k hk => hk ▸ h j hj⟩
  · intro h
    obtain ⟨j,hj⟩ := hJ
    exact ⟨(h j hj).1,fun k hk => (h k hk).2 k rfl⟩

theorem fiber_antitone (hJK : J ⊆ K) (y : X) : Fiber d f U K y ⊆ Fiber d f U J y :=
  fun _ hx => ⟨hx.1,fun i hi => hx.2 i (hJK hi)⟩

theorem fiber_singleton (i : I) (y : X) :
    Fiber d f U {i} y = {x ∈ U | d i (f x) y = 0} := by
  ext x; simp [Fiber]

theorem fiber_full_subset (i : I) (y : X) : Fiber d f U Set.univ y ⊆ Fiber d f U {i} y :=
  fiber_antitone (Set.subset_univ _) y

include symm tri in
theorem fiber_ident {i : I} (h : Ident (d i) f U) (y : X) :
    Fiber d f U {i} y = {x ∈ U | d i x y = 0} := by
  rw [fiber_singleton]
  ext x
  constructor
  · rintro ⟨hx,hd⟩
    exact ⟨hx, (zero_replace (symm i) (tri i) (h.2 x hx)).symm.trans hd⟩
  · rintro ⟨hx,hd⟩
    exact ⟨hx, (zero_replace (symm i) (tri i) (h.2 x hx)).trans hd⟩

theorem fiber_const (hc : ∀ j ∈ J, Const (d j) f U) {y : X} (hy : y ∈ f '' U) :
    Fiber d f U J y = U := by
  obtain ⟨z,hz,rfl⟩ := hy
  ext x
  exact ⟨fun h => h.1,fun hx => ⟨hx,fun j hj => hc j hj x hx z hz⟩⟩

include symm tri in
theorem fiber_const_empty {i : I} (hc : Const (d i) f U) {y z : X}
    (hz : z ∈ f '' U) (hpos : 0 < d i y z) : Fiber d f U {i} y = ∅ := by
  obtain ⟨a,ha,rfl⟩ := hz
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have he := zero_trans (tri i) ((symm i y (f x)).trans (hx.2 i rfl)) (hc x hx.1 a ha)
  exact (ne_of_gt hpos) he
end Fibers

/- Point-valued factorization includes empty restricted domains. -/
def Factors (f g : X → X) (U : Set X) : Prop :=
  ∃ T : (f '' U) → X, ∀ x (hx : x ∈ U), T ⟨f x,⟨x,hx,rfl⟩⟩ = g x

theorem factors_iff (f g : X → X) (U : Set X) : Factors f g U ↔ EqRel f U ⊆ EqRel g U := by
  classical
  constructor
  · rintro ⟨T,hT⟩ ⟨x,y⟩ ⟨hx,hy,he⟩
    refine ⟨hx,hy,?_⟩
    rw [← hT x hx, ← hT y hy]
    congr 1
    exact Subtype.ext he
  · intro h
    let rep : (f '' U) → X := fun z => Classical.choose z.property
    have hr (z : f '' U) : rep z ∈ U ∧ f (rep z) = z.val := Classical.choose_spec z.property
    refine ⟨fun z => g (rep z), ?_⟩
    intro x hx
    exact (h (show (rep ⟨f x,⟨x,hx,rfl⟩⟩, x) ∈ EqRel f U from
      ⟨(hr _).1,hx,(hr _).2⟩)).2.2

theorem mutual_factors_iff (f g : X → X) (U : Set X) :
    Factors f g U ∧ Factors g f U ↔ EqRel f U = EqRel g U := by
  rw [factors_iff, factors_iff]
  exact ⟨fun h => Set.Subset.antisymm h.1 h.2,fun h => ⟨h.le,h.ge⟩⟩

/- Legal radii are strictly positive and finite; the supremum is extended. -/
def Legal (di dout : X → X → ENNReal) (f : X → X) (U : Set X) (y : X)
    (r : ENNReal) : Prop := 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, di x y < r → dout (f x) (f y) = 0
noncomputable def Radius (di dout : X → X → ENNReal) (f : X → X) (U : Set X) (y : X) : ENNReal :=
  sSup {r | Legal di dout f U y r}
noncomputable def UniformOn (di dout : X → X → ENNReal) (f : X → X) (A U : Set X) : ENNReal :=
  ⨅ y ∈ A, Radius di dout f U y
noncomputable def Uniform (di dout : X → X → ENNReal) (f : X → X) (U : Set X) : ENNReal :=
  UniformOn di dout f U U
noncomputable def NullMatrix (d : I → X → X → ENNReal) (f : X → X) (U : Set X)
    (j i : I) : ENNReal := Uniform (d i) (d j) f U

theorem legal_ball_iff (di dout : X → X → ENNReal) (f : X → X) (U : Set X)
    (y : X) (r : ENNReal) :
    Legal di dout f U y r ↔ 0 < r ∧ r < ⊤ ∧
      ball di y r ∩ U ⊆ {x ∈ U | dout (f x) (f y) = 0} := by
  constructor
  · rintro ⟨h0,ht,h⟩
    exact ⟨h0,ht,fun x hx => ⟨hx.2,h x hx.2 hx.1⟩⟩
  · rintro ⟨h0,ht,h⟩
    exact ⟨h0,ht,fun x hx hd => (h ⟨hd,hx⟩).2⟩

theorem radius_empty_legal (di dout : X → X → ENNReal) (f : X → X) (U : Set X) (y : X)
    (h : ¬ ∃ r, Legal di dout f U y r) : Radius di dout f U y = 0 := by
  have he : {r | Legal di dout f U y r} = ∅ := by ext r; simp; exact fun hr => h ⟨r,hr⟩
  simp [Radius,he]

theorem below_radius {di dout : X → X → ENNReal} {f : X → X} {U : Set X} {x y : X}
    (hx : x ∈ U) (h : di x y < Radius di dout f U y) : dout (f x) (f y) = 0 := by
  obtain ⟨r,hr,hxr⟩ := lt_sSup_iff.mp h
  exact hr.2.2 x hx hxr

theorem radius_mono_domain {di dout : X → X → ENNReal} {f : X → X} {A B : Set X}
    (hBA : B ⊆ A) (y : X) : Radius di dout f A y ≤ Radius di dout f B y := by
  apply sSup_le_sSup
  rintro r ⟨h0,ht,h⟩
  exact ⟨h0,ht,fun x hx hd => h x (hBA hx) hd⟩

theorem uniform_le_radius {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    {y : X} (hy : y ∈ U) : Uniform di dout f U ≤ Radius di dout f U y :=
  iInf_le_of_le y (iInf_le_of_le hy le_rfl)

theorem uniform_mono_domain {di dout : X → X → ENNReal} {f : X → X} {A B : Set X}
    (hBA : B ⊆ A) : Uniform di dout f A ≤ Uniform di dout f B := by
  apply le_iInf; intro y
  apply le_iInf; intro hy
  exact (uniform_le_radius (hBA hy)).trans (radius_mono_domain hBA y)

theorem below_uniform {di dout : X → X → ENNReal} {f : X → X} {U : Set X} {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (h : di x y < Uniform di dout f U) : dout (f x) (f y) = 0 :=
  below_radius hx (h.trans_le (uniform_le_radius hy))

theorem separated_lower_bound {di dout : X → X → ENNReal} {f : X → X} {U : Set X} {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (h : 0 < dout (f x) (f y)) : Uniform di dout f U ≤ di x y := by
  by_contra hn
  exact (ne_of_gt h) (below_uniform hx hy (lt_of_not_ge hn))

theorem threshold_ball {di dout : X → X → ENNReal} {f : X → X} {U : Set X} {r : ENNReal}
    (hr : r ≤ Uniform di dout f U) {y : X} (hy : y ∈ U) :
    ball di y r ∩ U ⊆ {x ∈ U | dout (f x) (f y) = 0} := by
  intro x hx
  exact ⟨hx.2,below_uniform hx.2 hy (hx.1.trans_le hr)⟩

theorem const_radius {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    (hc : Const dout f U) {y : X} (hy : y ∈ U) : Radius di dout f U y = ⊤ := by
  apply top_unique
  apply le_of_forall_lt
  intro a ha
  obtain ⟨r,har,hrt⟩ := exists_between ha
  apply har.trans_le
  apply le_sSup
  exact ⟨(zero_le a).trans_lt har,hrt,fun x hx _ => hc x hx y hy⟩

theorem const_uniform {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    (hc : Const dout f U) : Uniform di dout f U = ⊤ := by
  apply top_unique
  apply le_iInf; intro y
  apply le_iInf; intro hy
  rw [const_radius hc hy]

theorem identity_radius_bound {di : X → X → ENNReal} {f : X → X} {U : Set X}
    (symm : ∀ x y, di x y = di y x) (tri : ∀ x y z, di x z ≤ di x y + di y z)
    (hi : Ident di f U) {y : X} (hy : y ∈ U) {r : ENNReal}
    (h0 : 0 < r) (ht : r < ⊤) (hgap : ∀ x ∈ U, di x y < r → di x y = 0) :
    r ≤ Radius di di f U y ∧ 0 < Radius di di f U y := by
  have hl : Legal di di f U y r := ⟨h0,ht,fun x hx hd =>
    (ident_isometry symm tri hi hx hy).trans (hgap x hx hd)⟩
  exact ⟨le_sSup hl,h0.trans_le (le_sSup hl)⟩

theorem composite_radius_mono {di dm dout : X → X → ENNReal} {f g : X → X}
    {U : Set X} (hz : ∀ a ∈ f '' U, ∀ b ∈ f '' U, dm a b = 0 → dout (g a) (g b) = 0) :
    Uniform di dm f U ≤ Uniform di dout (g ∘ f) U := by
  apply le_iInf; intro y
  apply le_iInf; intro hy
  apply (uniform_le_radius hy).trans
  apply sSup_le_sSup
  rintro r ⟨h0,ht,h⟩
  exact ⟨h0,ht,fun x hx hd => hz (f x) ⟨x,hx,rfl⟩ (f y) ⟨y,hy,rfl⟩ (h x hx hd)⟩

theorem radius_output_antitone {d : I → X → X → ENNReal} {di : X → X → ENNReal}
    {f : X → X} {U : Set X} {J K : Set I} (hJK : J ⊆ K) (y : X) :
    Radius di (subfamily_pseudometric d K) f U y ≤ Radius di (subfamily_pseudometric d J) f U y := by
  apply sSup_le_sSup
  rintro r ⟨h0,ht,h⟩
  refine ⟨h0,ht,?_⟩
  intro x hx hd
  apply (composite_zero d J _ _).mpr
  intro j hj
  exact (composite_zero d K _ _).mp (h x hx hd) j (hJK hj)

theorem uniform_output_antitone {d : I → X → X → ENNReal} {di : X → X → ENNReal}
    {f : X → X} {U : Set X} {J K : Set I} (hJK : J ⊆ K) :
    Uniform di (subfamily_pseudometric d K) f U ≤ Uniform di (subfamily_pseudometric d J) f U := by
  apply iInf_mono; intro y
  apply iInf_mono; intro _
  exact radius_output_antitone hJK y

/- Arbitrary, monotone input scale families, and the default diameter. -/
structure ScaleFamily (X I : Type) where
  value : I → {A : Set X // A.Nonempty} → ENNReal
  mono : ∀ i A B, A.val ⊆ B.val → value i A ≤ value i B
noncomputable def diameter (di : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, di x y

theorem diameter_mono {di : X → X → ENNReal} {A B : Set X} (h : A ⊆ B) :
    diameter di A ≤ diameter di B := by
  apply iSup_le; intro x
  apply iSup_le; intro hx
  apply iSup_le; intro y
  apply iSup_le; intro hy
  exact le_iSup_of_le x (le_iSup_of_le (h hx) (le_iSup_of_le y (le_iSup_of_le (h hy) le_rfl)))
noncomputable def diameterScale (d : I → X → X → ENNReal) : ScaleFamily X I :=
  ⟨fun i A => diameter (d i) A, fun _ _ _ h => diameter_mono h⟩
noncomputable def thresholdType (scale radius τs τn : ENNReal) : Bool × Bool :=
  (decide (scale < τs), decide (τn ≤ radius))

theorem threshold_type_iff (s r ts tn : ENNReal) (a b : Bool) :
    thresholdType s r ts tn = (a,b) ↔
    (a = true ↔ s < ts) ∧ (b = true ↔ tn ≤ r) := by
  cases a <;> cases b <;> simp [thresholdType]

theorem threshold_exhaustive (s r ts tn : ENNReal) :
    ∃! p : Bool × Bool, (p.1 = true ↔ s < ts) ∧ (p.2 = true ↔ tn ≤ r) := by
  refine ⟨thresholdType s r ts tn, ?_, ?_⟩
  · simp [thresholdType]
  · rintro ⟨a,b⟩ h
    exact ((threshold_type_iff s r ts tn a b).mpr h).symm

theorem scale_threshold_mono {s ts ts' : ENNReal} (h : ts ≤ ts') (hs : s < ts) : s < ts' := hs.trans_le h

theorem radius_threshold_antitone {r tn tn' : ENNReal} (h : tn ≤ tn') (hr : tn' ≤ r) : tn ≤ r := h.trans hr

theorem scale_domain_mono (σ : ScaleFamily X I) (i : I) (A B : {A : Set X // A.Nonempty})
    (h : B.val ⊆ A.val) (ts : ENNReal) : σ.value i B ≤ σ.value i A ∧
      (σ.value i A < ts → σ.value i B < ts) :=
  ⟨σ.mono i B A h,fun ht => (σ.mono i B A h).trans_lt ht⟩

theorem small_domain_iff {di dout : X → X → ENNReal} {f : X → X} {A : Set X}
    {ts tn : ENNReal} (hdiam : diameter di A < ts) (ht : ts ≤ tn) :
    tn ≤ Uniform di dout f A ↔ Const dout f A := by
  constructor
  · intro hr x hx y hy
    apply below_uniform hx hy
    have hd : di x y ≤ diameter di A :=
      le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
    exact ((hd.trans_lt hdiam).trans_le ht).trans_le hr
  · intro hc
    rw [const_uniform hc]
    exact le_top

theorem colip_gap_point {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    {K : ENNReal} (hK : 0 < K) (hco : ∀ x ∈ U, ∀ y ∈ U, K * di x y ≤ dout (f x) (f y))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) : ¬ (0 < di x y ∧ di x y < Radius di dout f U y) := by
  rintro ⟨hp,hr⟩
  have hzero := below_radius hx hr
  have hm : K * di x y = 0 := le_antisymm (by simpa [hzero] using hco x hx y hy) (zero_le _)
  exact (mul_ne_zero (ne_of_gt hK) (ne_of_gt hp)) hm

theorem colip_gap_uniform {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    {K : ENNReal} (hK : 0 < K) (hco : ∀ x ∈ U, ∀ y ∈ U, K * di x y ≤ dout (f x) (f y))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) : di x y = 0 ∨ Uniform di dout f U ≤ di x y := by
  by_cases hz : di x y = 0
  · exact Or.inl hz
  · right
    by_contra hn
    exact colip_gap_point hK hco hx hy ⟨pos_iff_ne_zero.mpr hz,
      (lt_of_not_ge hn).trans_le (uniform_le_radius hy)⟩

theorem le_radius_iff {di dout : X → X → ENNReal} {f : X → X} {U : Set X} {y : X} {a : ENNReal} :
    a ≤ Radius di dout f U y ↔ ∀ x ∈ U, di x y < a → dout (f x) (f y) = 0 := by
  constructor
  · intro h x hx hd
    exact below_radius hx (hd.trans_le h)
  · intro h
    apply le_of_forall_lt
    intro t ht
    obtain ⟨r,htr,hra⟩ := exists_between ht
    apply htr.trans_le
    apply le_sSup
    exact ⟨(zero_le t).trans_lt htr,hra.trans_le le_top,
      fun x hx hd => h x hx (hd.trans hra)⟩

theorem radius_components (d : I → X → X → ENNReal) (di : X → X → ENNReal)
    (f : X → X) (U : Set X) (J : Set I) (y : X) :
    Radius di (subfamily_pseudometric d J) f U y = ⨅ j ∈ J, Radius di (d j) f U y := by
  apply le_antisymm
  · apply le_iInf; intro j
    apply le_iInf; intro hj
    apply le_radius_iff.mpr
    intro x hx hd
    exact (composite_zero d J _ _).mp (below_radius hx hd) j hj
  · apply le_radius_iff.mpr
    intro x hx hd
    apply (composite_zero d J _ _).mpr
    intro j hj
    exact below_radius hx (hd.trans_le (iInf_le_of_le j (iInf_le_of_le hj le_rfl)))

theorem uniform_components (d : I → X → X → ENNReal) (di : X → X → ENNReal)
    (f : X → X) (U : Set X) (J : Set I) :
    Uniform di (subfamily_pseudometric d J) f U = ⨅ j ∈ J, Uniform di (d j) f U := by
  simp only [Uniform, UniformOn, radius_components]
  apply le_antisymm
  · apply le_iInf; intro j
    apply le_iInf; intro hj
    apply le_iInf; intro y
    apply le_iInf; intro hy
    exact iInf_le_of_le y (iInf_le_of_le hy (iInf_le_of_le j (iInf_le_of_le hj le_rfl)))
  · apply le_iInf; intro y
    apply le_iInf; intro hy
    apply le_iInf; intro j
    apply le_iInf; intro hj
    exact iInf_le_of_le j (iInf_le_of_le hj (iInf_le_of_le y (iInf_le_of_le hy le_rfl)))

theorem fiber_step {d : I → X → X → ENNReal} {f : X → X} {U : Set X} {i : I} {x y : X}
    (symm : ∀ a b, d i a b = d i b a) (hx : x ∈ Fiber d f U {i} (f y)) : d i (f y) (f x) = 0 :=
  (symm _ _).trans (hx.2 i rfl)

theorem radius_step {di dout : X → X → ENNReal} {f : X → X} {U : Set X} {x y : X}
    (si : ∀ a b, di a b = di b a) (so : ∀ a b, dout a b = dout b a)
    (hx : x ∈ U) (h : di y x < Radius di dout f U y) :
    (∃ r, Legal di dout f U y r ∧ di y x < r) ∧ dout (f y) (f x) = 0 := by
  constructor
  · exact lt_sSup_iff.mp h
  · rw [so]
    apply below_radius (di := di) hx
    rwa [si]

theorem composite_fiber_step {d : I → X → X → ENNReal} {f g : X → X} {U : Set X}
    {i : I} {x y : X} (symm : ∀ a b, d i a b = d i b a)
    (_hx : f x ∈ U) (_hy : f y ∈ U) (h : f y ∈ Fiber d g U {i} (g (f x))) :
    d i ((g ∘ f) x) ((g ∘ f) y) = 0 := by
  exact fiber_step (f := g) symm h

theorem identity_image_fiber {d : I → X → X → ENNReal} {f : X → X} {U : Set X}
    {i : I} (symm : ∀ a b, d i a b = d i b a)
    (tri : ∀ a b c, d i a c ≤ d i a b + d i b c) (hi : Ident (d i) f U)
    {y : X} (hy : y ∈ U) : Fiber d f U {i} (f y) = {x ∈ U | d i x y = 0} := by
  rw [fiber_singleton]
  ext x
  constructor
  · rintro ⟨hx,h⟩
    exact ⟨hx,(ident_isometry symm tri hi hx hy).symm.trans h⟩
  · rintro ⟨hx,h⟩
    exact ⟨hx,(ident_isometry symm tri hi hx hy).trans h⟩

theorem const_family_radii {d : I → X → X → ENNReal} {di : X → X → ENNReal}
    {f : X → X} {U : Set X} {J : Set I} (hc : ∀ j ∈ J, Const (d j) f U) :
    (∀ y ∈ U, Radius di (subfamily_pseudometric d J) f U y = ⊤) ∧
      Uniform di (subfamily_pseudometric d J) f U = ⊤ := by
  have h : Const (subfamily_pseudometric d J) f U := by
    intro x hx y hy
    exact (composite_zero d J _ _).mpr (fun j hj => hc j hj x hx y hy)
  exact ⟨fun _ hy => const_radius h hy,const_uniform h⟩

/- Finite compositions use the actual chainPrefix image, including length zero. -/
def chainPrefix (f : ℕ → X → X) : ℕ → X → X
  | 0 => id
  | n+1 => f n ∘ chainPrefix f n

theorem chainPrefix_domain_step (f : ℕ → X → X) (U : Set X) (n : ℕ) :
    chainPrefix f (n+1) '' U = f n '' (chainPrefix f n '' U) := by
  simp [chainPrefix,Set.image_image]

theorem active_chain {di : X → X → ENNReal}
    (self : ∀ x, di x x = 0) (symm : ∀ x y, di x y = di y x)
    (tri : ∀ x y z, di x z ≤ di x y + di y z)
    (f : ℕ → X → X) (U : Set X) (n : ℕ) :
    Active di (chainPrefix f n) U → ∃ k < n, Active di (f k) (chainPrefix f k '' U) := by
  induction n with
  | zero => exact fun h => (identity_not_active self U h).elim
  | succ n ih =>
    intro h
    rcases active_comp symm tri h with h | h
    · obtain ⟨k,hk,hka⟩ := ih h
      exact ⟨k,Nat.lt.step hk,hka⟩
    · exact ⟨n,Nat.lt_succ_self n,h⟩

theorem relation_chain {α : Type} (R : ℕ → Set α) (n : ℕ)
    (h : ∀ k < n, R k ⊆ R (k+1)) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ n) : R a ⊆ R b := by
  induction b, hab using Nat.le_induction with
  | base => exact Subset.rfl
  | succ b hab ih => exact (ih (Nat.le_trans (Nat.le_succ b) hb)).trans (h b (Nat.lt_of_succ_le hb))

theorem relation_chain_strict {α : Type} (R : ℕ → Set α) (n : ℕ)
    (h : ∀ k < n, R k ⊆ R (k+1)) {k : ℕ} (hk : k < n)
    (hs : R k ⊂ R (k+1)) : R 0 ⊂ R n ∧ ∃ p, p ∈ R n ∧ p ∉ R 0 := by
  obtain ⟨p,hp,hpn⟩ := Set.exists_of_ssubset hs
  have hkn := relation_chain R n h (Nat.succ_le_of_lt hk) le_rfl
  have h0k := relation_chain R n h (Nat.zero_le k) (Nat.le_of_lt hk)
  have hn : p ∉ R 0 := fun hp0 => hpn (h0k hp0)
  exact ⟨Set.ssubset_iff_subset_ne.mpr ⟨relation_chain R n h (Nat.zero_le n) le_rfl,
    fun he => hn (he ▸ hkn hp)⟩,p,hkn hp,hn⟩

/- A quotient is formed on the actual image, not on the entire ambient space. -/
def imageSetoid (d : I → X → X → ENNReal) (f : X → X) (U : Set X)
    (self : ∀ i x, d i x x = 0) (symm : ∀ i x y, d i x y = d i y x)
    (tri : ∀ i x y z, d i x z ≤ d i x y + d i y z) : Setoid (f '' U) where
  r a b := ∀ i, d i a b = 0
  iseqv := ⟨fun a i => self i a, fun h i => (symm i _ _).trans (h i),
    fun hab hbc i => zero_trans (tri i) (hab i) (hbc i)⟩

def ImageQuotient (d : I → X → X → ENNReal) (f : X → X) (U : Set X)
    (self : ∀ i x, d i x x = 0) (symm : ∀ i x y, d i x y = d i y x)
    (tri : ∀ i x y z, d i x z ≤ d i x y + d i y z) := Quotient (imageSetoid d f U self symm tri)

section Quotients
variable (d : I → X → X → ENNReal) (f g : X → X) (U : Set X)
variable (self : ∀ i x, d i x x = 0) (symm : ∀ i x y, d i x y = d i y x)
variable (tri : ∀ i x y z, d i x z ≤ d i x y + d i y z)

def imageClass (x : X) (hx : x ∈ U) : ImageQuotient d f U self symm tri :=
  Quotient.mk _ ⟨f x,⟨x,hx,rfl⟩⟩

def QuotientFactors : Prop :=
  ∃ T : ImageQuotient d f U self symm tri → ImageQuotient d g U self symm tri,
    ∀ x (hx : x ∈ U), T (imageClass d f U self symm tri x hx) = imageClass d g U self symm tri x hx

theorem quotient_factors_iff : QuotientFactors d f g U self symm tri ↔ ZeroRel d f U ⊆ ZeroRel d g U := by
  classical
  constructor
  · rintro ⟨T,hT⟩ ⟨x,y⟩ ⟨hx,hy,hxy⟩
    refine ⟨hx,hy,?_⟩
    have he : imageClass d f U self symm tri x hx = imageClass d f U self symm tri y hy := Quotient.sound hxy
    have ht := congrArg T he
    rw [hT x hx,hT y hy] at ht
    exact Quotient.exact ht
  · intro h
    let rep : (f '' U) → X := fun z => Classical.choose z.property
    have hr (z : f '' U) : rep z ∈ U ∧ f (rep z) = z.val := Classical.choose_spec z.property
    let F : (f '' U) → ImageQuotient d g U self symm tri :=
      fun z => imageClass d g U self symm tri (rep z) (hr z).1
    have hF : ∀ a b, (imageSetoid d f U self symm tri).r a b → F a = F b := by
      intro a b hab
      apply Quotient.sound
      apply (h (show (rep a,rep b) ∈ ZeroRel d f U from ?_)).2.2
      refine ⟨(hr a).1,(hr b).1,?_⟩
      intro i
      rw [(hr a).2,(hr b).2]
      exact hab i
    refine ⟨Quotient.lift F hF, ?_⟩
    intro x hx
    change F ⟨f x,⟨x,hx,rfl⟩⟩ = _
    apply Quotient.sound
    apply (h (show (rep ⟨f x,⟨x,hx,rfl⟩⟩,x) ∈ ZeroRel d f U from ?_)).2.2
    refine ⟨(hr _).1,hx,?_⟩
    intro i
    rw [(hr _).2]
    exact self i (f x)

theorem mutual_quotient_factors_iff :
    QuotientFactors d f g U self symm tri ∧ QuotientFactors d g f U self symm tri ↔
      ZeroRel d f U = ZeroRel d g U := by
  rw [quotient_factors_iff,quotient_factors_iff]
  exact ⟨fun h => Set.Subset.antisymm h.1 h.2,fun h => ⟨h.le,h.ge⟩⟩

include self in
theorem separated_relations
    (hs : ∀ a ∈ f '' U, ∀ b ∈ f '' U, (∀ i, d i a b = 0) → a = b) :
    ZeroRel d f U = EqRel f U := by
  ext ⟨x,y⟩
  constructor
  · rintro ⟨hx,hy,h⟩
    exact ⟨hx,hy,hs _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ h⟩
  · rintro ⟨hx,hy,h⟩
    exact ⟨hx,hy,fun i => h ▸ self i (f x)⟩

theorem separated_factorization
    (hf : ∀ a ∈ f '' U, ∀ b ∈ f '' U, (∀ i, d i a b = 0) → a = b)
    (hg : ∀ a ∈ g '' U, ∀ b ∈ g '' U, (∀ i, d i a b = 0) → a = b) :
    QuotientFactors d f g U self symm tri ↔ Factors f g U := by
  rw [quotient_factors_iff, separated_relations d f U self hf,
    separated_relations d g U self hg, factors_iff]

include symm in
theorem zero_relation_fiber {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x,y) ∈ ZeroRel d f U ↔ y ∈ Fiber d f U Set.univ (f x) := by
  constructor
  · rintro ⟨_,_,h⟩
    exact ⟨hy,fun i _ => (symm i _ _).trans (h i)⟩
  · rintro ⟨_,h⟩
    exact ⟨hx,hy,fun i => (symm i _ _).trans (h i trivial)⟩
end Quotients

theorem insufficient_radius_witness {di dout : X → X → ENNReal} {f : X → X}
    {A : Set X} {α : ENNReal} (h : Uniform di dout f A < α) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ ε : ENNReal, 0 < ε ∧ ε < ⊤ ∧ di x y < α ∧ ε ≤ dout (f x) (f y) := by
  classical
  have hw : ∃ x ∈ A, ∃ y ∈ A, di x y < α ∧ dout (f x) (f y) ≠ 0 := by
    by_contra hn
    push_neg at hn
    have hl : α ≤ Uniform di dout f A := by
      apply le_iInf; intro y
      apply le_iInf; intro hy
      apply le_radius_iff.mpr
      intro x hx hd
      exact hn x hx y hy hd
    exact (not_le_of_gt h) hl
  obtain ⟨x,hx,y,hy,hd,hn⟩ := hw
  have hp : 0 < min (dout (f x) (f y)) 1 := lt_min (pos_iff_ne_zero.mpr hn) zero_lt_one
  exact ⟨x,hx,y,hy,min (dout (f x) (f y)) 1,hp,
    (min_le_right _ _).trans_lt ENNReal.one_lt_top,hd,min_le_left _ _⟩

/- Uniform finite-cover transfer, with internal output centers. -/
theorem transfer_net {di dout : X → X → ENNReal} {f : X → X} {B : Set X}
    {δ ε : ENNReal} {C : Finset X}
    (h : ∀ x ∈ B, ∀ y ∈ B, di x y < δ → dout (f x) (f y) < ε)
    (hC : InternalEpsilonNet di δ B C) :
    ∃ D : Finset X, InternalEpsilonNet dout ε (f '' B) D ∧ D.card ≤ C.card := by
  classical
  refine ⟨C.image f, ?_,Finset.card_image_le⟩
  constructor
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨x,hC.1 hx,rfl⟩
  · rintro z ⟨x,hx,rfl⟩
    obtain ⟨c,hc,hd⟩ := hC.2 x hx
    exact ⟨f c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,h x hx c (hC.1 hc) hd⟩

theorem transfer_cover {di dout : X → X → ENNReal} {f : X → X} {B : Set X}
    {δ ε : ENNReal}
    (h : ∀ x ∈ B, ∀ y ∈ B, di x y < δ → dout (f x) (f y) < ε) :
    covering_number dout ε (f '' B) ≤ covering_number di δ B := by
  unfold covering_number
  apply le_iInf; intro C
  apply le_iInf; intro hC
  obtain ⟨D,hD,hcard⟩ := transfer_net h hC
  apply (iInf_le_of_le D (iInf_le_of_le hD le_rfl)).trans
  exact_mod_cast hcard

theorem null_cover_bound {di dout : X → X → ENNReal} {f : X → X} {A B : Set X}
    {τ ε : ENNReal} (hBA : B ⊆ A) (hτ : τ ≤ Uniform di dout f A) (hε : 0 < ε) :
    covering_number dout ε (f '' B) ≤ covering_number di τ B := by
  apply transfer_cover
  intro x hx y hy hd
  rw [below_uniform (hBA hx) (hBA hy) (hd.trans_le hτ)]
  exact hε

theorem const_cover_one {dout : X → X → ENNReal} {f : X → X} {U : Set X}
    (hc : Const dout f U) (hU : U.Nonempty) {ε : ENNReal} (hε : 0 < ε) :
    covering_number dout ε (f '' U) = 1 := by
  classical
  obtain ⟨a,ha⟩ := hU
  apply le_antisymm
  · have hn : InternalEpsilonNet dout ε (f '' U) {f a} := by
      constructor
      · simpa using (show f a ∈ f '' U from ⟨a,ha,rfl⟩)
      · rintro z ⟨x,hx,rfl⟩
        exact ⟨f a,Finset.mem_singleton_self _,by rw [hc x hx a ha]; exact hε⟩
    exact iInf_le_of_le {f a} (iInf_le_of_le hn (by simp))
  · exact one_le_covering_number_of_nonempty _ _ _ ⟨f a,⟨a,ha,rfl⟩⟩

theorem const_entropy_zero {dout : X → X → ENNReal} {f : X → X} {U : Set X}
    (hc : Const dout f U) (hU : U.Nonempty) {ε : ENNReal} (hε : 0 < ε) :
    metric_entropy dout ε (f '' U) = 0 := by
  simp [metric_entropy,const_cover_one hc hU hε,log2_ereal]

def TotallyBoundedBy (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ε < ⊤ → ∃ C : Finset X, InternalEpsilonNet d ε U C

theorem totally_bounded_iff (d : X → X → ENNReal) (U : Set X) :
    TotallyBoundedBy d U ↔ ∀ ε : ENNReal, 0 < ε → ε < ⊤ → covering_number d ε U < ⊤ := by
  constructor
  · intro h ε h0 ht
    exact lt_top_iff_ne_top.mpr (fun he => (covering_number_eq_top_iff d ε U).mp he (h ε h0 ht))
  · intro h ε h0 ht
    by_contra hn
    exact (ne_of_lt (h ε h0 ht)) ((covering_number_eq_top_iff d ε U).mpr hn)

theorem finite_cover_bound {d : X → X → ENNReal} (self : ∀ x, d x x = 0)
    {U : Set X} (hU : U.Finite) {ε : ENNReal} (hε : 0 < ε) :
    covering_number d ε U ≤ hU.toFinset.card := by
  classical
  have hn : InternalEpsilonNet d ε U hU.toFinset := by
    constructor
    · simp
    · intro x hx
      exact ⟨x,hU.mem_toFinset.mpr hx,by simpa [self x] using hε⟩
  exact iInf_le_of_le hU.toFinset (iInf_le_of_le hn le_rfl)

theorem finite_entropy_real {d : X → X → ENNReal} (self : ∀ x, d x x = 0)
    {U : Set X} (hU : U.Finite) (hn : U.Nonempty) {ε : ENNReal} (hε : 0 < ε) :
    0 < covering_number d ε U ∧ covering_number d ε U < ⊤ ∧
      ∃ r : ℝ, metric_entropy d ε U = (r : EReal) := by
  have hp := zero_lt_one.trans_le (one_le_covering_number_of_nonempty d ε U hn)
  have ht := (finite_cover_bound self hU hε).trans_lt (ENNReal.natCast_lt_top _)
  refine ⟨hp,ht,Real.logb 2 (covering_number d ε U).toReal,?_⟩
  simp [metric_entropy,log2_ereal,ne_of_gt hp,ne_of_lt ht]

/- Entropy differences require a proof of the original finiteness disjunction. -/
def DifferenceDefined (di dout : X → X → ENNReal) (f : X → X) (U : Set X) (ε : ENNReal) : Prop :=
  covering_number di ε U < ⊤ ∨ covering_number dout ε (f '' U) < ⊤
noncomputable def EntropyDifference (di dout : X → X → ENNReal) (f : X → X)
    (U : Set X) (ε : ENNReal) (_h : DifferenceDefined di dout f U ε) : EReal :=
  metric_entropy di ε U - metric_entropy dout ε (f '' U)

theorem entropy_difference_formula (di dout : X → X → ENNReal) (f : X → X)
    (U : Set X) (ε : ENNReal) (h : DifferenceDefined di dout f U ε) :
    EntropyDifference di dout f U ε h = metric_entropy di ε U - metric_entropy dout ε (f '' U) := rfl

theorem finite_difference_defined {di dout : X → X → ENNReal}
    (si : ∀ x, di x x = 0) (so : ∀ x, dout x x = 0) (f : X → X)
    {U : Set X} (hU : U.Finite) (hn : U.Nonempty) {ε : ENNReal} (hε : 0 < ε) :
    DifferenceDefined di dout f U ε ∧
    (∃ a : ℝ, metric_entropy di ε U = (a : EReal)) ∧
    (∃ b : ℝ, metric_entropy dout ε (f '' U) = (b : EReal)) := by
  have hi := finite_entropy_real si hU hn hε
  have ho := finite_entropy_real so (hU.image f) (hn.image f) hε
  exact ⟨Or.inl hi.2.1,hi.2.2,ho.2.2⟩

theorem const_difference {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    (hc : Const dout f U) (hU : U.Nonempty) {ε : ENNReal} (hε : 0 < ε) :
    ∃ h : DifferenceDefined di dout f U ε,
      EntropyDifference di dout f U ε h = metric_entropy di ε U := by
  have h : DifferenceDefined di dout f U ε := Or.inr (by
    rw [const_cover_one hc hU hε]; exact ENNReal.one_lt_top)
  exact ⟨h,by simp [EntropyDifference,const_entropy_zero hc hU hε]⟩

theorem log2_mono_positive {a b : ENNReal} (ha : 0 < a) (hab : a ≤ b) :
    log2_ereal a ≤ log2_ereal b := by
  have hb : 0 < b := ha.trans_le hab
  by_cases hbt : b = ⊤
  · simp [log2_ereal,hbt]
  have hat : a ≠ ⊤ := ne_of_lt (hab.trans_lt (lt_top_iff_ne_top.mpr hbt))
  simp only [log2_ereal,if_neg (ne_of_gt ha),if_neg (ne_of_gt hb),if_neg hat,if_neg hbt]
  apply EReal.coe_le_coe_iff.mpr
  exact (Real.logb_le_logb one_lt_two (ENNReal.toReal_pos (ne_of_gt ha) hat)
    (ENNReal.toReal_pos (ne_of_gt hb) hbt)).mpr (ENNReal.toReal_mono hbt hab)

theorem entropy_cover_mono {di dout : X → X → ENNReal} {A B : Set X} {δ ε : ENNReal}
    (hB : B.Nonempty) (h : covering_number dout ε B ≤ covering_number di δ A) :
    metric_entropy dout ε B ≤ metric_entropy di δ A :=
  log2_mono_positive (zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ hB)) h

theorem null_entropy_bound {di dout : X → X → ENNReal} {f : X → X} {A B : Set X}
    {τ ε : ENNReal} (hBA : B ⊆ A) (hB : B.Nonempty)
    (hτ : τ ≤ Uniform di dout f A) (hε : 0 < ε) :
    metric_entropy dout ε (f '' B) ≤ metric_entropy di τ B :=
  entropy_cover_mono (hB.image f) (null_cover_bound hBA hτ hε)

theorem pull_net {di dout : X → X → ENNReal} {f : X → X} {U : Set X} {δ ε : ENNReal}
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f x) (f y) < ε → di x y < δ)
    {C : Finset X} (hC : InternalEpsilonNet dout ε (f '' U) C) :
    ∃ D : Finset X, InternalEpsilonNet di δ U D ∧ D.card ≤ C.card := by
  classical
  let rep : X → X := fun z => if hz : z ∈ f '' U then Classical.choose hz else z
  have hr (z : X) (hz : z ∈ f '' U) : rep z ∈ U ∧ f (rep z) = z := by
    dsimp only [rep]
    rw [dif_pos hz]
    exact Classical.choose_spec hz
  refine ⟨C.image rep, ?_,Finset.card_image_le⟩
  constructor
  · intro y hy
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hy
    exact (hr z (hC.1 hz)).1
  · intro x hx
    obtain ⟨c,hc,hd⟩ := hC.2 (f x) ⟨x,hx,rfl⟩
    refine ⟨rep c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,h x hx (rep c) (hr c (hC.1 hc)).1 ?_⟩
    rwa [(hr c (hC.1 hc)).2]

theorem pull_cover {di dout : X → X → ENNReal} {f : X → X} {U : Set X} {δ ε : ENNReal}
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f x) (f y) < ε → di x y < δ) :
    covering_number di δ U ≤ covering_number dout ε (f '' U) := by
  unfold covering_number
  apply le_iInf; intro C
  apply le_iInf; intro hC
  obtain ⟨D,hD,hcard⟩ := pull_net h hC
  apply (iInf_le_of_le D (iInf_le_of_le hD le_rfl)).trans
  exact_mod_cast hcard

theorem ident_cover_entropy {di : X → X → ENNReal} {f : X → X} {U : Set X}
    (symm : ∀ x y, di x y = di y x) (tri : ∀ x y z, di x z ≤ di x y + di y z)
    (hi : Ident di f U) (ε : ENNReal) :
    covering_number di ε (f '' U) = covering_number di ε U ∧
    metric_entropy di ε (f '' U) = metric_entropy di ε U := by
  have he : covering_number di ε (f '' U) = covering_number di ε U := by
    apply le_antisymm
    · apply transfer_cover
      intro x hx y hy h
      rwa [ident_isometry symm tri hi hx hy]
    · apply pull_cover
      intro x hx y hy h
      rwa [ident_isometry symm tri hi hx hy] at h
  exact ⟨he,congrArg log2_ereal he⟩

theorem entropy_finite_iff {d : X → X → ENNReal} {U : Set X} (hU : U.Nonempty) (ε : ENNReal) :
    metric_entropy d ε U ≠ ⊤ ↔ covering_number d ε U < ⊤ := by
  have hz := ne_of_gt (zero_lt_one.trans_le (one_le_covering_number_of_nonempty d ε U hU))
  by_cases ht : covering_number d ε U = ⊤
  · simp [metric_entropy,log2_ereal,ht]
  · simp [metric_entropy,log2_ereal,hz,ht,lt_top_iff_ne_top]

theorem difference_no_indeterminate {di dout : X → X → ENNReal} {f : X → X}
    {U : Set X} (hU : U.Nonempty) {ε : ENNReal} (h : DifferenceDefined di dout f U ε) :
    ¬ (metric_entropy di ε U = ⊤ ∧ metric_entropy dout ε (f '' U) = ⊤) := by
  rintro ⟨hi,ho⟩
  rcases h with h | h
  · exact (entropy_finite_iff hU ε).mpr h hi
  · exact (entropy_finite_iff (hU.image f) ε).mpr h ho

theorem difference_top {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    (hU : U.Nonempty) {ε : ENNReal} (h : DifferenceDefined di dout f U ε)
    (ht : metric_entropy di ε U = ⊤) : EntropyDifference di dout f U ε h = ⊤ := by
  unfold EntropyDifference
  rw [ht]
  exact EReal.top_sub (fun ho => difference_no_indeterminate hU h ⟨ht,ho⟩)

theorem difference_bottom {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    {ε : ENNReal} (h : DifferenceDefined di dout f U ε)
    (ht : metric_entropy dout ε (f '' U) = ⊤) : EntropyDifference di dout f U ε h = ⊥ := by
  simp [EntropyDifference,ht]

theorem difference_real {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    {ε : ENNReal} (h : DifferenceDefined di dout f U ε) {a b : ℝ}
    (hi : metric_entropy di ε U = (a : EReal)) (ho : metric_entropy dout ε (f '' U) = (b : EReal)) :
    EntropyDifference di dout f U ε h = ((a-b : ℝ) : EReal) := by
  simp [EntropyDifference,hi,ho]

theorem ident_difference_zero {di : X → X → ENNReal} {f : X → X} {U : Set X}
    (symm : ∀ x y, di x y = di y x) (tri : ∀ x y z, di x z ≤ di x y + di y z)
    (hi : Ident di f U) (hU : U.Nonempty) (ε : ENNReal) (h : DifferenceDefined di di f U ε) :
    EntropyDifference di di f U ε h = 0 := by
  have he := (ident_cover_entropy symm tri hi ε).2
  have ht : metric_entropy di ε U ≠ ⊤ := by
    intro ht
    exact difference_no_indeterminate hU h ⟨ht,he.trans ht⟩
  have hb : metric_entropy di ε U ≠ ⊥ := ne_of_gt (lt_of_lt_of_le (by simp) (metric_entropy_nonneg di ε U hU))
  simp only [EntropyDifference,he]
  exact EReal.sub_self ht hb

theorem lip_transfer {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    {L : ENNReal} (hL0 : 0 < L) (hLt : L < ⊤)
    (hL : ∀ x ∈ U, ∀ y ∈ U, dout (f x) (f y) ≤ L * di x y) (ε : ENNReal) :
    (∀ C, InternalEpsilonNet di (ε / L) U C →
      ∃ D, InternalEpsilonNet dout ε (f '' U) D ∧ D.card ≤ C.card) ∧
    covering_number dout ε (f '' U) ≤ covering_number di (ε / L) U := by
  have h : ∀ x ∈ U, ∀ y ∈ U, di x y < ε / L → dout (f x) (f y) < ε := by
    intro x hx y hy hd
    apply (hL x hx y hy).trans_lt
    rw [mul_comm]
    exact ENNReal.mul_lt_of_lt_div hd
  exact ⟨fun _ hC => transfer_net h hC, transfer_cover h⟩

theorem colip_transfer {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    {K : ENNReal} (hK0 : 0 < K) (hKt : K < ⊤)
    (hK : ∀ x ∈ U, ∀ y ∈ U, K * di x y ≤ dout (f x) (f y)) (ε : ENNReal) :
    (∀ C, InternalEpsilonNet dout ε (f '' U) C →
      ∃ D, InternalEpsilonNet di (ε / K) U D ∧ D.card ≤ C.card) ∧
    covering_number di (ε / K) U ≤ covering_number dout ε (f '' U) := by
  have h : ∀ x ∈ U, ∀ y ∈ U, dout (f x) (f y) < ε → di x y < ε / K := by
    intro x hx y hy hd
    apply (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hK0)) (Or.inl (ne_of_lt hKt))).mpr
    rw [mul_comm]
    exact (hK x hx y hy).trans_lt hd
  exact ⟨fun _ hC => pull_net h hC, pull_cover h⟩

theorem composite_lip_radius {di dm dout : X → X → ENNReal} {f g : X → X} {U : Set X}
    {L : ENNReal} (hL0 : 0 < L) (hLt : L < ⊤)
    (hL : ∀ x ∈ U, ∀ y ∈ U, dm (f x) (f y) ≤ L * di x y) :
    Uniform dm dout g (f '' U) / L ≤ Uniform di dout (g ∘ f) U := by
  apply le_iInf; intro y
  apply le_iInf; intro hy
  apply le_radius_iff.mpr
  intro x hx hd
  apply below_uniform (di := dm) (f := g) (U := f '' U) ⟨x,hx,rfl⟩ ⟨y,hy,rfl⟩
  apply (hL x hx y hy).trans_lt
  rw [mul_comm]
  exact ENNReal.mul_lt_of_lt_div hd

theorem sparse_row_const {d : I → X → X → ENNReal} {f g : X → X} {U : Set X}
    {j : I} (L : I → ENNReal) (hc : Const (d j) f U)
    (hrow : ∀ k, k ≠ j → L k = 0)
    (hL : ∀ a ∈ f '' U, ∀ b ∈ f '' U,
      d j (g a) (g b) ≤ ∑' k, L k * d k a b) : Const (d j) (g ∘ f) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  have hz : (∑' k, L k * d k (f x) (f y)) = 0 := by
    have hall : ∀ k, L k * d k (f x) (f y) = 0 := by
      intro k
      by_cases hk : k = j
      · subst k; simp [hc x hx y hy]
      · simp [hrow k hk]
    simp only [hall,tsum_zero]
  simpa [hz] using hL (f x) ⟨x,hx,rfl⟩ (f y) ⟨y,hy,rfl⟩

theorem factor_lip {di : X → X → ENNReal} {f g : X → X} {U : Set X}
    {K L : ENNReal} (hK0 : 0 < K) (hKt : K < ⊤) (_hLt : L < ⊤)
    (hK : ∀ x ∈ U, ∀ y ∈ U, K * di x y ≤ di (f x) (f y))
    (hL : ∀ x ∈ U, ∀ y ∈ U, di (g x) (g y) ≤ L * di x y)
    (T : (f '' U) → X) (hT : ∀ x (hx : x ∈ U), T ⟨f x,⟨x,hx,rfl⟩⟩ = g x)
    (a b : f '' U) : di (T a) (T b) ≤ (L / K) * di a b := by
  obtain ⟨x,hx,hfx⟩ := a.property
  obtain ⟨y,hy,hfy⟩ := b.property
  have ha : (⟨f x,⟨x,hx,rfl⟩⟩ : f '' U) = a := Subtype.ext hfx
  have hb : (⟨f y,⟨y,hy,rfl⟩⟩ : f '' U) = b := Subtype.ext hfy
  have hxy : di x y ≤ di (f x) (f y) / K := by
    apply (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hK0)) (Or.inl (ne_of_lt hKt))).mpr
    simpa [mul_comm] using hK x hx y hy
  calc
    di (T a) (T b) = di (g x) (g y) := by rw [← ha,← hb,hT x hx,hT y hy]
    _ ≤ L * di x y := hL x hx y hy
    _ ≤ L * (di (f x) (f y) / K) := mul_le_mul_left' hxy L
    _ = (L / K) * di a b := by rw [hfx,hfy]; simp only [div_eq_mul_inv]; ac_rfl

theorem lip_entropy_bound {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    (hU : U.Nonempty) (hTB : TotallyBoundedBy di U) {L ε : ENNReal}
    (hL0 : 0 < L) (hLt : L < ⊤) (hε0 : 0 < ε) (hεt : ε < ⊤)
    (hL : ∀ x ∈ U, ∀ y ∈ U, dout (f x) (f y) ≤ L * di x y) :
    metric_entropy di ε U ≠ ⊤ ∧ metric_entropy dout ε (f '' U) ≠ ⊤ ∧
    ∃ h : DifferenceDefined di dout f U ε,
      metric_entropy di ε U - metric_entropy di (ε/L) U ≤ EntropyDifference di dout f U ε h := by
  have hδ0 := ENNReal.div_pos (ne_of_gt hε0) (ne_of_lt hLt)
  have hδt := ENNReal.div_lt_top (ne_of_lt hεt) (ne_of_gt hL0)
  have hi := (totally_bounded_iff di U).mp hTB ε hε0 hεt
  have hδ := (totally_bounded_iff di U).mp hTB (ε/L) hδ0 hδt
  have hc := (lip_transfer hL0 hLt hL ε).2
  have ho := hc.trans_lt hδ
  refine ⟨(entropy_finite_iff hU ε).mpr hi,
    (entropy_finite_iff (hU.image f) ε).mpr ho,Or.inl hi,?_⟩
  exact EReal.sub_le_sub le_rfl (entropy_cover_mono (hU.image f) hc)

theorem colip_entropy_bound {di dout : X → X → ENNReal} {f : X → X} {U : Set X}
    (hU : U.Nonempty) (hTB : TotallyBoundedBy di U) {K ε : ENNReal}
    (hK0 : 0 < K) (hKt : K < ⊤) (hε0 : 0 < ε) (hεt : ε < ⊤)
    (hK : ∀ x ∈ U, ∀ y ∈ U, K * di x y ≤ dout (f x) (f y)) :
    ∃ h : DifferenceDefined di dout f U ε,
      EntropyDifference di dout f U ε h ≤ metric_entropy di ε U - metric_entropy di (ε/K) U := by
  have hi := (totally_bounded_iff di U).mp hTB ε hε0 hεt
  refine ⟨Or.inl hi,?_⟩
  exact EReal.sub_le_sub le_rfl (entropy_cover_mono hU (colip_transfer hK0 hKt hK ε).2)

theorem finite_difference_real {di dout : X → X → ENNReal}
    (si : ∀ x, di x x = 0) (so : ∀ x, dout x x = 0) (f : X → X)
    {U : Set X} (hU : U.Finite) (hn : U.Nonempty) {ε : ENNReal} (hε : 0 < ε) :
    ∃ h : DifferenceDefined di dout f U ε, ∃ r : ℝ, EntropyDifference di dout f U ε h = (r : EReal) := by
  obtain ⟨h,⟨a,ha⟩,⟨b,hb⟩⟩ := finite_difference_defined si so f hU hn hε
  exact ⟨h,a-b,difference_real h ha hb⟩

namespace Examples
/- A three-point absorbing extension of the two-point metric. -/
def twoDist : Option Bool → Option Bool → ENNReal
  | none,none => 0
  | some a,some b => if a = b then 0 else 1
  | _,_ => ⊤

theorem twoDist_lawful : ExtendedPseudoMetric (Option Bool) none twoDist := by
  constructor
  · exact ⟨some false,by simp⟩
  · intro x; cases x <;> simp [twoDist]
  · intro x y
    cases x with
    | none => cases y <;> simp [twoDist]
    | some a => cases y with
      | none => simp [twoDist]
      | some b => simp [twoDist,eq_comm]
  · intro x y z
    cases x with
    | none => cases y <;> cases z <;> simp [twoDist]
    | some a => cases y with
      | none => cases z <;> simp [twoDist]
      | some b => cases z with
        | none => simp [twoDist]
        | some c => cases a <;> cases b <;> cases c <;> norm_num [twoDist]
  · intro x hx; cases x <;> simp_all [twoDist]

def swap : Operator (Option Bool) none :=
  ⟨Option.map Bool.not,rfl⟩
def twoDomain : Set (Option Bool) := {some false,some true}

theorem mem_twoDomain (x : Option Bool) : x ∈ twoDomain ↔ x ≠ none := by
  cases x with
  | none => simp [twoDomain]
  | some b => cases b <;> simp [twoDomain]

theorem swap_domain : twoDomain ⊆ dom swap := by
  intro x hx
  cases x with
  | none => simp [twoDomain] at hx
  | some b => simp [dom,swap]

theorem swap_image : swap.func '' twoDomain = twoDomain := by
  ext x
  cases x with
  | none => simp [twoDomain,swap]
  | some b => cases b <;> simp [twoDomain,swap]

theorem swap_twice : swap.func ∘ swap.func = id := by
  funext x
  cases x <;> simp [swap]

theorem swap_active : Active twoDist swap.func twoDomain := by
  intro h
  rcases h with hc | hi
  · have hh := hc (some false) (by simp [twoDomain]) (some true) (by simp [twoDomain])
    norm_num [swap,twoDist] at hh
  · have hh := hi.2 (some false) (by simp [twoDomain])
    norm_num [swap,twoDist] at hh

theorem id_ident : Ident twoDist id twoDomain := by
  constructor
  · intro hc
    have hh := hc (some false) (by simp [twoDomain]) (some true) (by simp [twoDomain])
    norm_num [twoDist] at hh
  · intro x hx
    exact twoDist_lawful.dist_self x

theorem swap_counterexample :
    Active twoDist swap.func twoDomain ∧ Active twoDist swap.func (swap.func '' twoDomain) ∧
    ¬ Ident twoDist swap.func twoDomain ∧
    ¬ Ident twoDist swap.func (swap.func '' twoDomain) ∧
    Ident twoDist (swap.func ∘ swap.func) twoDomain ∧
    ¬ Active twoDist (swap.func ∘ swap.func) twoDomain := by
  rw [swap_image,swap_twice]
  exact ⟨swap_active,swap_active,fun h => swap_active (Or.inr h),
    fun h => swap_active (Or.inr h),id_ident,fun h => h (Or.inr id_ident)⟩

noncomputable def infiniteDist (x y : Option Bool) : ENNReal := if x = y then 0 else ⊤

theorem infiniteDist_lawful : ExtendedPseudoMetric (Option Bool) none infiniteDist := by
  classical
  constructor
  · exact ⟨some false,by simp⟩
  · intro x; simp [infiniteDist]
  · intro x y; simp [infiniteDist,eq_comm]
  · intro x y z
    by_cases hxy : x = y
    · subst y; simp [infiniteDist]
    · simp [infiniteDist,hxy]
  · intro x hx; simp [infiniteDist,hx]

def identityOp : Operator (Option Bool) none := ⟨id,rfl⟩
noncomputable def twoGauge (i : Bool) : Option Bool → Option Bool → ENNReal :=
  if i = false then infiniteDist else twoDist

theorem twoGauge_lawful (i : Bool) : ExtendedPseudoMetric (Option Bool) none (twoGauge i) := by
  cases i
  · exact infiniteDist_lawful
  · exact twoDist_lawful

theorem identity_domain : twoDomain ⊆ dom identityOp := by
  intro x hx
  exact (mem_twoDomain x).mp hx

theorem infinite_input_radius (j : Bool) (y : Option Bool) :
    Radius (twoGauge false) (twoGauge j) identityOp.func twoDomain y = ⊤ := by
  apply top_unique
  apply le_radius_iff.mpr
  intro x hx hd
  have hxy : x = y := by
    by_contra hn
    simp [twoGauge,infiniteDist,hn] at hd
  subst x
  exact (twoGauge_lawful j).dist_self y

theorem infinite_input_uniform (j : Bool) :
    NullMatrix twoGauge identityOp.func twoDomain j false = ⊤ := by
  apply top_unique
  apply le_iInf; intro y
  apply le_iInf; intro hy
  rw [infinite_input_radius]

theorem identity_not_const (j : Bool) : ¬ Const (twoGauge j) identityOp.func twoDomain := by
  intro h
  have hh := h (some false) (by simp [twoDomain]) (some true) (by simp [twoDomain])
  cases j <;> norm_num [twoGauge,infiniteDist,twoDist,identityOp] at hh

theorem infinite_radius_counterexample :
    (NullMatrix twoGauge identityOp.func twoDomain false false = ⊤ ∧
      ¬ Const (twoGauge false) identityOp.func twoDomain) ∧
    (NullMatrix twoGauge identityOp.func twoDomain true false = ⊤ ∧
      ¬ Const (twoGauge true) identityOp.func twoDomain) :=
  ⟨⟨infinite_input_uniform false,identity_not_const false⟩,
    ⟨infinite_input_uniform true,identity_not_const true⟩⟩
end Examples

theorem finite_inf_attained (J : Finset I) (hJ : J.Nonempty) (a : I → ENNReal) :
    ∃ j ∈ J, (⨅ k ∈ (J : Set I), a k) = a j ∧ ∀ k ∈ J, a j ≤ a k := by
  obtain ⟨j,hj,hmin⟩ := J.exists_min_image a hJ
  refine ⟨j,hj,le_antisymm ?_ ?_,hmin⟩
  · exact iInf_le_of_le j (iInf_le_of_le hj le_rfl)
  · apply le_iInf; intro k
    apply le_iInf; intro hk
    exact hmin k hk

theorem radius_component_minimum (d : I → X → X → ENNReal) (di : X → X → ENNReal)
    (f : X → X) (U : Set X) (J : Finset I) (hJ : J.Nonempty) (y : X) :
    ∃ j ∈ J, Radius di (subfamily_pseudometric d J) f U y = Radius di (d j) f U y ∧
      ∀ k ∈ J, Radius di (d j) f U y ≤ Radius di (d k) f U y := by
  rw [radius_components]
  exact finite_inf_attained J hJ _

theorem uniform_component_minimum (d : I → X → X → ENNReal) (i : I)
    (f : X → X) (U : Set X) (J : Finset I) (hJ : J.Nonempty) :
    ∃ j ∈ J, Uniform (d i) (subfamily_pseudometric d J) f U = NullMatrix d f U j i ∧
      ∀ k ∈ J, NullMatrix d f U j i ≤ NullMatrix d f U k i := by
  rw [uniform_components]
  exact finite_inf_attained J hJ _

theorem point_constant_selfcomp {bot : X} (f : Operator X bot) (U : Set X) (c : X)
    (hc : ∀ x ∈ U, f.func x = c) :
    (∀ x ∈ U, (f.func ∘ f.func) x = f.func c) ∧
    (∀ x ∈ U, ∀ y ∈ U, (f.func ∘ f.func) x = (f.func ∘ f.func) y) ∧
    (f.func c ≠ bot → U ⊆ dom (f * f)) ∧
    (f.func c = bot → U ∩ dom (f * f) = ∅) := by
  have he : ∀ x ∈ U, (f.func ∘ f.func) x = f.func c := fun x hx => congrArg f.func (hc x hx)
  refine ⟨he,fun x hx y hy => (he x hx).trans (he y hy).symm,?_,?_⟩
  · intro h x hx
    change f.func (f.func x) ≠ bot
    simpa [hc x hx] using h
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hd⟩
    apply hd
    exact (he x hx).trans h

noncomputable def ChannelType (d : I → X → X → ENNReal) (σ : ScaleFamily X I)
    (f : X → X) (A : {A : Set X // A.Nonempty}) (τs τn : ENNReal) (i j : I) : Bool × Bool :=
  thresholdType (σ.value i A) (NullMatrix d f A j i) τs τn

theorem channel_type_formula (d : I → X → X → ENNReal) (σ : ScaleFamily X I)
    (f : X → X) (A : {A : Set X // A.Nonempty}) (τs τn : ENNReal) (i j : I) :
    ChannelType d σ f A τs τn i j =
      (decide (σ.value i A < τs), decide (τn ≤ Uniform (d i) (d j) f A)) := rfl

theorem Examples.swap_composite_domain : Examples.twoDomain ⊆ dom (Examples.swap * Examples.swap) := by
  intro x hx
  change (Examples.swap.func ∘ Examples.swap.func) x ≠ none
  rw [Examples.swap_twice]
  exact (Examples.mem_twoDomain x).mp hx

namespace Supplement
open formal_oet.vol_01.ch_01_foundations

noncomputable def absorbDist {A : Type} (d : A → A → ENNReal) : Option A → Option A → ENNReal
  | none, none => 0
  | some x, some y => d x y
  | _, _ => ⊤

theorem absorbDist_lawful {A : Type} (a : A) (d : A → A → ENNReal)
    (hself : ∀ x, d x x = 0) (hsymm : ∀ x y, d x y = d y x)
    (htri : ∀ x y z, d x z ≤ d x y + d y z) :
    ExtendedPseudoMetric (Option A) none (absorbDist d) := by
  constructor
  · exact ⟨some a,by simp⟩
  · intro x; cases x <;> simp [absorbDist,hself]
  · intro x y; cases x <;> cases y <;> simp [absorbDist,hsymm]
  · intro x y z
    cases x <;> cases y <;> cases z <;> simp [absorbDist,htri]
  · intro x hx; cases x <;> simp_all [absorbDist]

noncomputable def readingDist {A : Type} (r : A → ℝ) : Option A → Option A → ENNReal :=
  absorbDist (fun x y => edist (r x) (r y))

theorem readingDist_lawful {A : Type} (a : A) (r : A → ℝ) :
    ExtendedPseudoMetric (Option A) none (readingDist r) :=
  absorbDist_lawful a _ (fun _ => edist_self _) (fun _ _ => edist_comm _ _)
    (fun _ _ _ => edist_triangle _ _ _)

noncomputable def absDist : Option ℝ → Option ℝ → ENNReal := readingDist abs
noncomputable def realDist : Option ℝ → Option ℝ → ENNReal := readingDist id

theorem absDist_formula (x y : ℝ) : absDist (some x) (some y) = ENNReal.ofReal (abs (abs x - abs y)) := by
  simp [absDist,readingDist,absorbDist,edist_dist,Real.dist_eq]

theorem realDist_formula (x y : ℝ) : realDist (some x) (some y) = ENNReal.ofReal (|x-y|) := by
  simp [realDist,readingDist,absorbDist,edist_dist,Real.dist_eq]

theorem absDist_lawful : ExtendedPseudoMetric (Option ℝ) none absDist := readingDist_lawful 0 abs
theorem realDist_lawful : ExtendedPseudoMetric (Option ℝ) none realDist := readingDist_lawful 0 id

def affine : Operator (Option ℝ) none := ⟨Option.map (fun x => 2*x-1),rfl⟩
def zeroOne : Set (Option ℝ) := {some 0,some 1}

theorem affine_domain : zeroOne ⊆ dom affine ∧ zeroOne ⊆ dom (affine * affine) := by
  constructor <;> intro x hx <;> rcases hx with hx | hx <;> rcases hx with rfl <;>
    simp [dom,affine,HMul.hMul,Mul.mul,operator_compose]

theorem affine_constant : Const absDist affine.func zeroOne := by
  intro x hx y hy
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hx with rfl <;> rcases hy with rfl <;>
    norm_num [affine,absDist,readingDist,absorbDist,edist_dist,Real.dist_eq]

theorem affine_fiber :
    Fiber (fun _ : Unit => absDist) affine.func zeroOne {()} (affine.func (some 0)) = zeroOne := by
  apply fiber_const
  · intro j hj; exact affine_constant
  · exact ⟨some 0,by simp [zeroOne],rfl⟩

theorem affine_component : Const absDist affine.func zeroOne ∧
    ¬ Ident absDist affine.func zeroOne ∧ ¬ Active absDist affine.func zeroOne :=
  ⟨affine_constant,fun h => h.1 affine_constant,fun h => h (Or.inl affine_constant)⟩

theorem affine_squared_fiber :
    Fiber (fun _ : Unit => absDist) (affine.func ∘ affine.func) zeroOne {()}
      ((affine.func ∘ affine.func) (some 0)) = {some 0} := by
  rw [fiber_singleton]
  ext x
  constructor
  · rintro ⟨hx,hd⟩
    rcases hx with hx | hx
    · exact hx
    · rcases hx with rfl
      norm_num [affine,absDist,readingDist,absorbDist,edist_dist,Real.dist_eq] at hd
  · rintro rfl
    exact ⟨by simp [zeroOne],absDist_lawful.dist_self _⟩

theorem affine_squared_component : Active absDist (affine.func ∘ affine.func) zeroOne := by
  rintro (hc | hi)
  · have h := hc (some 0) (by simp [zeroOne]) (some 1) (by simp [zeroOne])
    norm_num [affine,absDist,readingDist,absorbDist,edist_dist,Real.dist_eq] at h
  · have h := hi.2 (some 0) (by simp [zeroOne])
    norm_num [affine,absDist,readingDist,absorbDist,edist_dist,Real.dist_eq] at h

/- Seven points are none and the six labels a,b,p,q,r,s. -/
noncomputable def discreteRead {A B : Type} (r : A → B) (x y : A) : ENNReal :=
  by classical exact if r x = r y then 0 else 1

theorem discreteRead_lawful {A B : Type} (a : A) (r : A → B) :
    ExtendedPseudoMetric (Option A) none (absorbDist (discreteRead r)) := by
  classical
  apply absorbDist_lawful a
  · intro x; simp [discreteRead]
  · intro x y; simp [discreteRead,eq_comm]
  · intro x y z
    by_cases hxy : r x = r y
    · simp [discreteRead,hxy]
    · by_cases hyz : r y = r z
      · simp [discreteRead,hyz]
      · simp [discreteRead,hxy,hyz]
        split_ifs <;> norm_num

inductive Six where
  | a | b | p | q | r | s
  deriving DecidableEq

def collapsedRead (x : Six) : Six := if x = .q then .p else x
noncomputable def sevenGauge (i : Bool) : Option Six → Option Six → ENNReal :=
  if i = false then absorbDist (discreteRead collapsedRead) else absorbDist (discreteRead id)

theorem sevenGauge_lawful (i : Bool) : ExtendedPseudoMetric (Option Six) none (sevenGauge i) := by
  cases i
  · exact discreteRead_lawful .a collapsedRead
  · exact discreteRead_lawful .a id

def sevenInner : Operator (Option Six) none :=
  ⟨fun x => match x with
    | some .a => some .p
    | some .b => some .q
    | _ => none,rfl⟩
def sevenOuter : Operator (Option Six) none :=
  ⟨fun x => match x with
    | some .p => some .r
    | some .q => some .s
    | _ => none,rfl⟩
def sevenDomain : Set (Option Six) := {some .a,some .b}

theorem seven_domain_legal : sevenDomain ⊆ dom (sevenOuter * sevenInner) := by
  intro x hx
  rcases hx with hx | hx <;> rcases hx with rfl <;>
    simp [dom,sevenInner,sevenOuter,HMul.hMul,Mul.mul,operator_compose]

theorem seven_image : sevenInner.func '' sevenDomain = {some .p,some .q} := by
  simp [sevenDomain,Set.image_insert_eq,Set.image_singleton,sevenInner]

theorem seven_inner_constant : Const (sevenGauge false) sevenInner.func sevenDomain := by
  intro x hx y hy
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hx with rfl <;> rcases hy with rfl <;>
    simp [sevenInner,sevenGauge,absorbDist,discreteRead,collapsedRead]

theorem seven_composite_not_constant : ¬ Const (sevenGauge false) (sevenOuter.func ∘ sevenInner.func) sevenDomain := by
  intro hc
  have h := hc (some .a) (by simp [sevenDomain]) (some .b) (by simp [sevenDomain])
  norm_num [sevenInner,sevenOuter,sevenGauge,absorbDist,discreteRead,collapsedRead] at h
  simp_all

theorem seven_other_component_separates :
    sevenGauge true (sevenInner.func (some .a)) (sevenInner.func (some .b)) = 1 ∧
    sevenGauge false ((sevenOuter.func ∘ sevenInner.func) (some .a))
      ((sevenOuter.func ∘ sevenInner.func) (some .b)) = 1 := by
  simp [sevenInner,sevenOuter,sevenGauge,absorbDist,discreteRead,collapsedRead]

def realIdentity : Operator (Option ℝ) none := ⟨id,rfl⟩

theorem real_two_point_scale_counterexample :
    ({some (0 : ℝ)} : Set (Option ℝ)) ⊆ zeroOne ∧ zeroOne ⊆ dom realIdentity ∧
    ({some (0 : ℝ)} : Set (Option ℝ)).Nonempty ∧ zeroOne.Nonempty ∧
    diameter realDist {some (0 : ℝ)} = 0 ∧ diameter realDist zeroOne = 1 ∧
    diameter realDist {some (0 : ℝ)} < (1/2 : ENNReal) ∧
      ¬ diameter realDist zeroOne < (1/2 : ENNReal) := by
  have hB : diameter realDist {some (0 : ℝ)} = 0 := by
    simp [diameter,realDist,readingDist,absorbDist]
  have hA : diameter realDist zeroOne = 1 := by
    apply le_antisymm
    · apply iSup_le; intro x
      apply iSup_le; intro hx
      apply iSup_le; intro y
      apply iSup_le; intro hy
      rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hx with rfl <;> rcases hy with rfl <;>
        norm_num [realDist,readingDist,absorbDist,edist_dist,Real.dist_eq]
    · have he : realDist (some 0) (some 1) = 1 := by
        norm_num [realDist,readingDist,absorbDist,edist_dist,Real.dist_eq]
      rw [← he]
      exact le_iSup_of_le (some 0) (le_iSup_of_le (by simp [zeroOne])
        (le_iSup_of_le (some 1) (le_iSup_of_le (by simp [zeroOne]) le_rfl)))
  refine ⟨?_,?_,?_,?_,hB,hA,?_,?_⟩
  · intro x hx; rcases hx with rfl; simp [zeroOne]
  · intro x hx
    rcases hx with hx | hx <;> rcases hx with rfl <;> simp [dom,realIdentity]
  · exact ⟨some 0,rfl⟩
  · exact ⟨some 0,by simp [zeroOne]⟩
  · rw [hB]; norm_num
  · rw [hA]; norm_num

/- Translation example: exact input-fiber partitions, with duplicate fibers removed. -/
def translation : Operator (Option ℝ) none := ⟨Option.map (fun x => x+1),rfl⟩
def translationDomain : Set (Option ℝ) := {some (-3),some (-2),some 0,some 2}

theorem translation_domain : translationDomain ⊆ dom translation ∧ translationDomain ⊆ dom realIdentity := by
  constructor <;> intro x hx <;>
    rcases hx with hx | hx | hx | hx <;> rcases hx with rfl <;> simp [dom,translation,realIdentity]

theorem singleton_fiber_insert {A : Type} (d : A → A → ENNReal) (f : A → A)
    (a y : A) (U : Set A) :
    Fiber (fun _ : Unit => d) f (insert a U) {()} y =
      (if d (f a) y = 0 then {a} else ∅) ∪ Fiber (fun _ : Unit => d) f U {()} y := by
  classical
  ext x
  simp only [fiber_singleton,Set.mem_setOf_eq,Set.mem_insert_iff,Set.mem_union]
  by_cases h : d (f a) y = 0
  · simp only [h,if_true,Set.mem_singleton_iff]
    constructor
    · rintro ⟨rfl | hx,hd⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hx,hd⟩
    · rintro (rfl | ⟨hx,hd⟩)
      · exact ⟨Or.inl rfl,h⟩
      · exact ⟨Or.inr hx,hd⟩
  · simp only [h,if_false,Set.mem_empty_iff_false,false_or]
    constructor
    · rintro ⟨rfl | hx,hd⟩
      · exact (h hd).elim
      · exact ⟨hx,hd⟩
    · exact fun ⟨hx,hd⟩ => ⟨Or.inr hx,hd⟩

@[simp] theorem singleton_fiber_empty {A : Type} (d : A → A → ENNReal) (f : A → A) (y : A) :
    Fiber (fun _ : Unit => d) f ∅ {()} y = ∅ := by ext x; simp [Fiber]

theorem singleton_domain_fiber {A : Type} (d : A → A → ENNReal) (f : A → A) (a y : A) :
    Fiber (fun _ : Unit => d) f {a} {()} y = (if d (f a) y = 0 then {a} else ∅) := by
  classical
  simpa using singleton_fiber_insert d f a y ∅

theorem identity_translation_domain_fibers :
    Fiber (fun _ : Unit => absDist) id translationDomain {()} (some (-3)) = {some (-3)} ∧
    Fiber (fun _ : Unit => absDist) id translationDomain {()} (some (-2)) = {some (-2),some 2} ∧
    Fiber (fun _ : Unit => absDist) id translationDomain {()} (some 0) = {some 0} ∧
    Fiber (fun _ : Unit => absDist) id translationDomain {()} (some 2) = {some (-2),some 2} := by
  norm_num [translationDomain,singleton_fiber_insert,singleton_domain_fiber,Set.pair_comm,absDist,readingDist,absorbDist,edist_dist,Real.dist_eq]

theorem translation_fibers :
    Fiber (fun _ : Unit => absDist) translation.func translationDomain {()} (translation.func (some (-3))) = {some (-3)} ∧
    Fiber (fun _ : Unit => absDist) translation.func translationDomain {()} (translation.func (some (-2))) = {some (-2),some 0} ∧
    Fiber (fun _ : Unit => absDist) translation.func translationDomain {()} (translation.func (some 0)) = {some (-2),some 0} ∧
    Fiber (fun _ : Unit => absDist) translation.func translationDomain {()} (translation.func (some 2)) = {some 2} := by
  norm_num [translationDomain,singleton_fiber_insert,singleton_domain_fiber,Set.pair_comm,translation,absDist,readingDist,absorbDist,edist_dist,Real.dist_eq]

theorem translation_input_cover : covering_number absDist (3/2) translationDomain = 2 := by
  classical
  apply le_antisymm
  · let C : Finset (Option ℝ) := {some (-2),some 0}
    have hC : InternalEpsilonNet absDist (3/2) translationDomain C := by
      constructor
      · intro c hc
        change c ∈ C at hc
        simp only [C,Finset.mem_insert,Finset.mem_singleton] at hc
        rcases hc with rfl | rfl <;> simp [translationDomain]
      · intro x hx
        rcases hx with hx | hx | hx | hx <;> rcases hx with rfl
        · exact ⟨some (-2),by simp [C],by norm_num [absDist_formula,ENNReal.lt_div_iff_mul_lt]⟩
        · exact ⟨some (-2),by simp [C],by norm_num [absDist_formula,ENNReal.lt_div_iff_mul_lt]⟩
        · exact ⟨some 0,by simp [C],by norm_num [absDist_formula,ENNReal.lt_div_iff_mul_lt]⟩
        · exact ⟨some (-2),by simp [C],by norm_num [absDist_formula,ENNReal.lt_div_iff_mul_lt]⟩
    exact iInf_le_of_le C (iInf_le_of_le hC (by norm_num [C]))
  · apply le_iInf; intro C
    apply le_iInf; intro hC
    obtain ⟨c0,hc0,hd0⟩ := hC.2 (some 0) (by simp [translationDomain])
    obtain ⟨c3,hc3,hd3⟩ := hC.2 (some (-3)) (by simp [translationDomain])
    have hne : c0 ≠ c3 := by
      intro h
      subst c3
      have hm := hC.1 hc0
      rcases hm with hm | hm | hm | hm <;> rcases hm with rfl <;>
        first
        | (solve | norm_num [absDist_formula,ENNReal.lt_div_iff_mul_lt] at hd0)
        | (solve | norm_num [absDist_formula,ENNReal.lt_div_iff_mul_lt] at hd3)
    exact_mod_cast Nat.succ_le_of_lt (Finset.one_lt_card.mpr ⟨c0,hc0,c3,hc3,hne⟩)

theorem translation_output_cover : covering_number absDist (3/2) (translation.func '' translationDomain) = 1 := by
  classical
  apply le_antisymm
  · let C : Finset (Option ℝ) := {some (-2)}
    have hC : InternalEpsilonNet absDist (3/2) (translation.func '' translationDomain) C := by
      constructor
      · intro c hc
        have hc' : c = some (-2) := Finset.mem_singleton.mp hc
        subst c
        exact ⟨some (-3),by simp [translationDomain],by norm_num [translation]⟩
      · rintro z ⟨x,hx,rfl⟩
        refine ⟨some (-2),by simp [C],?_⟩
        rcases hx with hx | hx | hx | hx <;> rcases hx with rfl <;>
          norm_num [translation,absDist,readingDist,absorbDist,edist_dist,Real.dist_eq,ENNReal.lt_div_iff_mul_lt]
    exact iInf_le_of_le C (iInf_le_of_le hC (by simp [C]))
  · apply one_le_covering_number_of_nonempty
    exact ⟨translation.func (some 0),⟨some 0,by simp [translationDomain],rfl⟩⟩

theorem translation_entropy_difference :
    ∃ h : DifferenceDefined absDist absDist translation.func translationDomain (3/2),
      EntropyDifference absDist absDist translation.func translationDomain (3/2) h = 1 := by
  have h : DifferenceDefined absDist absDist translation.func translationDomain (3/2) := by
    left; rw [translation_input_cover]; norm_num
  refine ⟨h,?_⟩
  norm_num [EntropyDifference,metric_entropy,translation_input_cover,translation_output_cover,log2_ereal]

noncomputable def stepOp : Operator (Option ℝ) none :=
  ⟨Option.map (fun x => if x < 0 then 0 else 1),rfl⟩
def stepDomain : Set (Option ℝ) :=
  some '' {x : ℝ | (-1 ≤ x ∧ x < 0) ∨ (0 < x ∧ x ≤ 1)}

theorem step_domain_legal : stepDomain.Nonempty ∧ stepDomain ⊆ dom stepOp := by
  constructor
  · exact ⟨some (-1),⟨-1,by norm_num,rfl⟩⟩
  · rintro x ⟨r,hr,rfl⟩
    simp [dom,stepOp]

theorem step_formula (x : ℝ) : stepOp.func (some x) = some (if x < 0 then 0 else 1) := rfl

theorem diameter_pair {A : Type} (d : A → A → ENNReal) (a b : A)
    (hs : ∀ x, d x x = 0) (hsy : ∀ x y, d x y = d y x) :
    diameter d {a,b} = d a b := by
  apply le_antisymm
  · apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hx with rfl <;> rcases hy with rfl
    · simp [hs]
    · exact le_rfl
    · rw [hsy]
    · simp [hs]
  · exact le_iSup_of_le a (le_iSup_of_le (by simp)
      (le_iSup_of_le b (le_iSup_of_le (by simp) le_rfl)))

noncomputable def floorOp : Operator (Option ℝ) none := ⟨Option.map (fun x => (⌊x⌋ : ℝ)),rfl⟩
def zeroTwo : Set (Option ℝ) := {some 0,some 2}

theorem floor_domain (S : Set ℝ) : some '' S ⊆ dom floorOp := by
  rintro x ⟨r,hr,rfl⟩
  simp [dom,floorOp]

theorem zeroTwo_domain : zeroTwo.Nonempty ∧ zeroTwo ⊆ dom floorOp := by
  constructor
  · exact ⟨some 0,by simp [zeroTwo]⟩
  · intro x hx
    rcases hx with hx | hx <;> rcases hx with rfl <;> simp [dom,floorOp]

theorem zeroTwo_diameter : diameter realDist zeroTwo = 2 := by
  rw [zeroTwo,diameter_pair realDist _ _ realDist_lawful.dist_self realDist_lawful.symm]
  norm_num [realDist_formula]

theorem zeroTwo_floor_radius (y : Option ℝ) (hy : y ∈ zeroTwo) :
    Radius realDist realDist floorOp.func zeroTwo y = 2 := by
  apply le_antisymm
  · by_contra hn
    have hr : 2 < Radius realDist realDist floorOp.func zeroTwo y := lt_of_not_ge hn
    rcases hy with hy | hy <;> rcases hy with rfl
    · have he := below_radius (di := realDist) (dout := realDist) (f := floorOp.func)
        (U := zeroTwo) (x := some 2) (y := some 0) (by simp [zeroTwo])
        (by simpa [realDist_formula] using hr)
      norm_num [floorOp,realDist,readingDist,absorbDist,edist_dist,Real.dist_eq] at he
    · have he := below_radius (di := realDist) (dout := realDist) (f := floorOp.func)
        (U := zeroTwo) (x := some 0) (y := some 2) (by simp [zeroTwo])
        (by simpa [realDist_formula] using hr)
      norm_num [floorOp,realDist,readingDist,absorbDist,edist_dist,Real.dist_eq] at he
  · apply le_radius_iff.mpr
    intro x hx hd
    rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hx with rfl <;> rcases hy with rfl <;>
      first
      | (solve | norm_num [realDist_formula] at hd)
      | (solve | norm_num [floorOp,realDist,readingDist,absorbDist,edist_dist,Real.dist_eq])

theorem zeroTwo_floor_uniform : Uniform realDist realDist floorOp.func zeroTwo = 2 := by
  apply le_antisymm
  · exact (uniform_le_radius (show some 0 ∈ zeroTwo by simp [zeroTwo])).trans
      (le_of_eq (zeroTwo_floor_radius _ (by simp [zeroTwo])))
  · apply le_iInf; intro y
    apply le_iInf; intro hy
    rw [zeroTwo_floor_radius y hy]

theorem zeroTwo_floor_type :
    thresholdType (diameter realDist zeroTwo) (Uniform realDist realDist floorOp.func zeroTwo) 1 1 = (false,true) := by
  rw [zeroTwo_diameter,zeroTwo_floor_uniform]
  norm_num [thresholdType]

theorem floor_positive_radius_not_constant :
    (1 : ENNReal) ≤ Uniform realDist realDist floorOp.func zeroTwo ∧
      ¬ Const realDist floorOp.func zeroTwo := by
  constructor
  · rw [zeroTwo_floor_uniform]; norm_num
  · intro hc
    have h := hc (some 0) (by simp [zeroTwo]) (some 2) (by simp [zeroTwo])
    norm_num [floorOp,realDist,readingDist,absorbDist,edist_dist,Real.dist_eq] at h

def realInterval (a b : ℝ) : Set (Option ℝ) := some '' Set.Icc a b

theorem realInterval_diameter {a b : ℝ} (hab : a ≤ b) :
    diameter realDist (realInterval a b) = ENNReal.ofReal (b-a) := by
  apply le_antisymm
  · apply iSup_le; intro x
    apply iSup_le; rintro ⟨x,hx,rfl⟩
    apply iSup_le; intro y
    apply iSup_le; rintro ⟨y,hy,rfl⟩
    rw [realDist_formula]
    apply ENNReal.ofReal_le_ofReal
    apply abs_le.mpr
    constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]
  · have hd : realDist (some a) (some b) = ENNReal.ofReal (b-a) := by
      rw [realDist_formula,abs_of_nonpos (sub_nonpos.mpr hab)]
      congr 1; ring
    rw [← hd]
    exact le_iSup_of_le (some a) (le_iSup_of_le ⟨a,⟨le_rfl,hab⟩,rfl⟩
      (le_iSup_of_le (some b) (le_iSup_of_le ⟨b,⟨hab,le_rfl⟩,rfl⟩ le_rfl)))

theorem realInterval_nonempty {a b : ℝ} (hab : a ≤ b) : (realInterval a b).Nonempty :=
  ⟨some a,⟨a,⟨le_rfl,hab⟩,rfl⟩⟩

theorem floor_half_constant : Const realDist floorOp.func (realInterval 0 (1/2)) := by
  rintro x ⟨x,hx,rfl⟩ y ⟨y,hy,rfl⟩
  have hfx : ⌊x⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr ⟨by simpa using hx.1,by norm_num; linarith [hx.2]⟩
  have hfy : ⌊y⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr ⟨by simpa using hy.1,by norm_num; linarith [hy.2]⟩
  simp [floorOp,hfx,hfy,realDist,readingDist,absorbDist]

theorem floor_half_data :
    diameter realDist (realInterval 0 (1/2)) = ENNReal.ofReal (1/2) ∧
    Uniform realDist realDist floorOp.func (realInterval 0 (1/2)) = ⊤ ∧
    thresholdType (diameter realDist (realInterval 0 (1/2)))
      (Uniform realDist realDist floorOp.func (realInterval 0 (1/2))) 1 1 = (true,true) := by
  have hd := realInterval_diameter (show (0 : ℝ) ≤ 1/2 by norm_num)
  have hu := const_uniform (di := realDist) floor_half_constant
  refine ⟨by simpa using hd,hu,?_⟩
  rw [hd,hu]
  norm_num [thresholdType]

theorem floor_crossing_radius_zero :
    Radius realDist realDist floorOp.func (realInterval (9/10) (11/10)) (some 1) = 0 := by
  by_contra hn
  have hp : 0 < Radius realDist realDist floorOp.func (realInterval (9/10) (11/10)) (some 1) := pos_iff_ne_zero.mpr hn
  obtain ⟨r,hr,_⟩ := lt_sSup_iff.mp hp
  have hrpos : 0 < r.toReal := ENNReal.toReal_pos (ne_of_gt hr.1) (ne_of_lt hr.2.1)
  let δ : ℝ := min (r.toReal/2) (1/20)
  have hδpos : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδsmall : δ ≤ 1/20 := min_le_right _ _
  have hδr : δ < r.toReal := (min_le_left _ _).trans_lt (by linarith)
  have hx : some (1-δ) ∈ realInterval (9/10) (11/10) :=
    ⟨1-δ,⟨by linarith,by linarith⟩,rfl⟩
  have hdist : realDist (some (1-δ)) (some 1) < r := by
    rw [realDist_formula]
    have he : |(1-δ)-1| = δ := by rw [abs_of_nonpos (by linarith)]; ring
    rw [he]
    exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hδpos) (ne_of_lt hr.2.1)).mpr hδr
  have hz := hr.2.2 (some (1-δ)) hx hdist
  have hfloor : ⌊1-δ⌋ = (0 : ℤ) := Int.floor_eq_iff.mpr ⟨by norm_num; linarith,by norm_num; linarith⟩
  norm_num [floorOp,hfloor,realDist,readingDist,absorbDist,edist_dist,Real.dist_eq] at hz

theorem floor_crossing_uniform_zero :
    Uniform realDist realDist floorOp.func (realInterval (9/10) (11/10)) = 0 := by
  apply le_antisymm _ (zero_le _)
  have hy : some (1 : ℝ) ∈ realInterval (9/10) (11/10) := ⟨1,by norm_num,rfl⟩
  exact (uniform_le_radius hy).trans (le_of_eq floor_crossing_radius_zero)

theorem floor_crossing_data :
    diameter realDist (realInterval (9/10) (11/10)) = ENNReal.ofReal (1/5) ∧
    Uniform realDist realDist floorOp.func (realInterval (9/10) (11/10)) = 0 ∧
    thresholdType (diameter realDist (realInterval (9/10) (11/10)))
      (Uniform realDist realDist floorOp.func (realInterval (9/10) (11/10))) 1 1 = (true,false) := by
  have hd := realInterval_diameter (show (9/10 : ℝ) ≤ 11/10 by norm_num)
  refine ⟨by norm_num at hd ⊢; exact hd,floor_crossing_uniform_zero,?_⟩
  rw [hd,floor_crossing_uniform_zero]
  norm_num [thresholdType]

theorem floor_wide_uniform_zero : Uniform realDist realDist floorOp.func (realInterval 0 2) = 0 := by
  apply le_antisymm _ (zero_le _)
  have hsub : realInterval (9/10) (11/10) ⊆ realInterval 0 2 := by
    rintro x ⟨x,hx,rfl⟩
    exact ⟨x,⟨by linarith [hx.1],by linarith [hx.2]⟩,rfl⟩
  exact (uniform_mono_domain (di := realDist) (dout := realDist) (f := floorOp.func) hsub).trans
    (le_of_eq floor_crossing_uniform_zero)

theorem floor_wide_data :
    diameter realDist (realInterval 0 2) = 2 ∧
    Uniform realDist realDist floorOp.func (realInterval 0 2) = 0 ∧
    thresholdType (diameter realDist (realInterval 0 2))
      (Uniform realDist realDist floorOp.func (realInterval 0 2)) 1 1 = (false,false) := by
  have hd := realInterval_diameter (show (0 : ℝ) ≤ 2 by norm_num)
  refine ⟨by simpa using hd,floor_wide_uniform_zero,?_⟩
  rw [hd,floor_wide_uniform_zero]
  norm_num [thresholdType]

theorem step_real_nonzero {y : ℝ} (hy : (-1 ≤ y ∧ y < 0) ∨ (0 < y ∧ y ≤ 1)) : y ≠ 0 := by
  rcases hy with hy | hy <;> linarith

theorem step_lower_radius {y : ℝ} (hy : (-1 ≤ y ∧ y < 0) ∨ (0 < y ∧ y ≤ 1)) :
    ENNReal.ofReal |y| ≤ Radius realDist realDist stepOp.func stepDomain (some y) := by
  apply le_radius_iff.mpr
  rintro _ ⟨x,hx,rfl⟩ hd
  rw [realDist_formula] at hd
  have hyd : 0 < |y| := abs_pos.mpr (step_real_nonzero hy)
  have hdist : |x-y| < |y| := (ENNReal.ofReal_lt_ofReal_iff hyd).mp hd
  by_cases hyneg : y < 0 <;> by_cases hxneg : x < 0
  · simp [stepOp,hyneg,hxneg,realDist,readingDist,absorbDist]
  · rw [abs_of_neg hyneg,abs_of_nonneg (by linarith)] at hdist
    linarith
  · have hypos : 0 < y := lt_of_le_of_ne (le_of_not_gt hyneg) (Ne.symm (step_real_nonzero hy))
    rw [abs_of_pos hypos,abs_of_neg (by linarith)] at hdist
    linarith
  · simp [stepOp,hyneg,hxneg,realDist,readingDist,absorbDist]

theorem step_point_radius {y : ℝ} (hy : (-1 ≤ y ∧ y < 0) ∨ (0 < y ∧ y ≤ 1)) :
    Radius realDist realDist stepOp.func stepDomain (some y) = ENNReal.ofReal |y| := by
  apply le_antisymm _ (step_lower_radius hy)
  by_contra hn
  have hlt := lt_of_not_ge hn
  obtain ⟨t,ht0,hty,htr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hlt
  have htpos : 0 < t := by
    have he : 0 < ENNReal.ofReal t := (zero_le _).trans_lt hty
    exact ENNReal.ofReal_pos.mp he
  have hyt : |y| < t := (ENNReal.ofReal_lt_ofReal_iff htpos).mp hty
  let δ : ℝ := min ((t-|y|)/2) (1/2)
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ ≤ 1/2 := min_le_right _ _
  have hδt : |y| + δ < t := by have hh := min_le_left ((t-|y|)/2) (1/2); dsimp [δ]; linarith
  by_cases hyneg : y < 0
  · have hx : some δ ∈ stepDomain := ⟨δ,Or.inr ⟨hδpos,by linarith⟩,rfl⟩
    have hd : realDist (some δ) (some y) < Radius realDist realDist stepOp.func stepDomain (some y) := by
      apply lt_trans _ htr
      rw [realDist_formula]
      apply (ENNReal.ofReal_lt_ofReal_iff htpos).mpr
      rw [abs_of_pos (show 0 < δ-y by linarith)]
      rw [abs_of_neg hyneg] at hδt
      linarith
    have hz := below_radius hx hd
    norm_num [stepOp,hyneg,not_lt_of_ge (le_of_lt hδpos),realDist,readingDist,absorbDist,edist_dist,Real.dist_eq] at hz
  · have hypos : 0 < y := lt_of_le_of_ne (le_of_not_gt hyneg) (Ne.symm (step_real_nonzero hy))
    have hx : some (-δ) ∈ stepDomain := ⟨-δ,Or.inl ⟨by linarith,by linarith⟩,rfl⟩
    have hd : realDist (some (-δ)) (some y) < Radius realDist realDist stepOp.func stepDomain (some y) := by
      apply lt_trans _ htr
      rw [realDist_formula]
      apply (ENNReal.ofReal_lt_ofReal_iff htpos).mpr
      rw [abs_of_neg (by linarith)]
      rw [abs_of_pos hypos] at hδt
      linarith
    have hz := below_radius hx hd
    norm_num [stepOp,hyneg,show -δ < 0 by linarith,realDist,readingDist,absorbDist,edist_dist,Real.dist_eq] at hz

theorem legal_iff_radius_bound {A : Type} (di dout : A → A → ENNReal) (f : A → A)
    (U : Set A) (y : A) (r : ENNReal) :
    Legal di dout f U y r ↔ 0 < r ∧ r < ⊤ ∧ r ≤ Radius di dout f U y := by
  constructor
  · intro h
    exact ⟨h.1,h.2.1,le_sSup h⟩
  · rintro ⟨h0,ht,hr⟩
    exact ⟨h0,ht,fun x hx hd => below_radius hx (hd.trans_le hr)⟩

theorem step_legal_radii {y : ℝ} (hy : (-1 ≤ y ∧ y < 0) ∨ (0 < y ∧ y ≤ 1)) (r : ENNReal) :
    Legal realDist realDist stepOp.func stepDomain (some y) r ↔ 0 < r ∧ r ≤ ENNReal.ofReal |y| := by
  rw [legal_iff_radius_bound,step_point_radius hy]
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,h.2.trans_lt ENNReal.ofReal_lt_top,h.2⟩⟩

theorem step_point_radius_positive {y : ℝ} (hy : (-1 ≤ y ∧ y < 0) ∨ (0 < y ∧ y ≤ 1)) :
    0 < Radius realDist realDist stepOp.func stepDomain (some y) := by
  rw [step_point_radius hy]
  exact ENNReal.ofReal_pos.mpr (abs_pos.mpr (step_real_nonzero hy))

theorem step_uniform_zero : Uniform realDist realDist stepOp.func stepDomain = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_forall_gt
  intro b hb
  obtain ⟨t,ht0,htp,htb⟩ := ENNReal.lt_iff_exists_real_btwn.mp hb
  have ht : 0 < t := ENNReal.ofReal_pos.mp htp
  let δ : ℝ := min (t/2) (1/2)
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδsmall : δ ≤ 1/2 := min_le_right _ _
  have hδt : δ < t := (min_le_left _ _).trans_lt (by linarith)
  have hy : (-1 ≤ δ ∧ δ < 0) ∨ (0 < δ ∧ δ ≤ 1) := Or.inr ⟨hδpos,by linarith⟩
  have hmem : some δ ∈ stepDomain := ⟨δ,hy,rfl⟩
  calc
    Uniform realDist realDist stepOp.func stepDomain ≤ Radius realDist realDist stepOp.func stepDomain (some δ) := uniform_le_radius hmem
    _ = ENNReal.ofReal δ := by rw [step_point_radius hy,abs_of_pos hδpos]
    _ < ENNReal.ofReal t := (ENNReal.ofReal_lt_ofReal_iff ht).mpr hδt
    _ < b := htb

theorem zeroOne_cover_half : covering_number realDist (1/2) zeroOne = 2 := by
  classical
  apply le_antisymm
  · let C : Finset (Option ℝ) := {some 0,some 1}
    have hC : InternalEpsilonNet realDist (1/2) zeroOne C := by
      constructor
      · intro c hc
        change c ∈ C at hc
        simpa [C,zeroOne] using hc
      · intro x hx
        refine ⟨x,?_,?_⟩
        · simpa [C,zeroOne] using hx
        · rw [realDist_lawful.dist_self]; norm_num
    exact iInf_le_of_le C (iInf_le_of_le hC (by norm_num [C]))
  · apply le_iInf; intro C
    apply le_iInf; intro hC
    obtain ⟨a,ha,hd0⟩ := hC.2 (some 0) (by simp [zeroOne])
    obtain ⟨b,hb,hd1⟩ := hC.2 (some 1) (by simp [zeroOne])
    have hne : a ≠ b := by
      intro he
      subst b
      have hm := hC.1 ha
      rcases hm with hm | hm <;> rcases hm with rfl
      · norm_num [realDist_formula,ENNReal.lt_div_iff_mul_lt] at hd1
      · norm_num [realDist_formula,ENNReal.lt_div_iff_mul_lt] at hd0
    exact_mod_cast Nat.succ_le_of_lt (Finset.one_lt_card.mpr ⟨a,ha,b,hb,hne⟩)

theorem step_cover_counterexample (τ : ENNReal) (hτ0 : 0 < τ) (hτt : τ < ⊤) :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2*a) < τ ∧
      ({some (-a),some a} : Set (Option ℝ)) ⊆ stepDomain ∧
      covering_number realDist τ {some (-a),some a} = 1 ∧
      covering_number realDist (1/2) (stepOp.func '' {some (-a),some a}) = 2 := by
  classical
  have hτ : 0 < τ.toReal := ENNReal.toReal_pos (ne_of_gt hτ0) (ne_of_lt hτt)
  let a : ℝ := min (τ.toReal/4) 1
  have ha : 0 < a := lt_min (by linarith) zero_lt_one
  have ha1 : a ≤ 1 := min_le_right _ _
  have h2a : 2*a < τ.toReal := by have hh := min_le_left (τ.toReal/4) 1; dsimp [a]; linarith
  have hd : ENNReal.ofReal (2*a) < τ :=
    (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) (ne_of_lt hτt)).mpr h2a
  have hsub : ({some (-a),some a} : Set (Option ℝ)) ⊆ stepDomain := by
    intro x hx
    rcases hx with hx | hx <;> rcases hx with rfl
    · exact ⟨-a,Or.inl ⟨by linarith,by linarith⟩,rfl⟩
    · exact ⟨a,Or.inr ⟨ha,ha1⟩,rfl⟩
  refine ⟨a,ha,ha1,hd,hsub,?_,?_⟩
  · apply le_antisymm
    · have hC : InternalEpsilonNet realDist τ {some (-a),some a} {some a} := by
        constructor
        · intro c hc
          have he : c = some a := Finset.mem_singleton.mp hc
          subst c; simp
        · intro x hx
          refine ⟨some a,by simp,?_⟩
          rcases hx with hx | hx <;> rcases hx with rfl
          · rw [realDist_formula,abs_of_neg (by linarith)]
            convert hd using 2 <;> ring
          · rw [realDist_lawful.dist_self]; exact hτ0
      exact iInf_le_of_le {some a} (iInf_le_of_le hC (by simp))
    · exact one_le_covering_number_of_nonempty _ _ _ ⟨some a,by simp⟩
  · have him : stepOp.func '' {some (-a),some a} = zeroOne := by
      simp [Set.image_insert_eq,Set.image_singleton,stepOp,show -a < 0 by linarith,not_lt_of_ge (le_of_lt ha),zeroOne]
    rw [him,zeroOne_cover_half]

/- Four-point rearrangement example, including every open-ball endpoint. -/
def fourDomain : Set (Option ℝ) := {some 0,some 1,some 2,some 3}
noncomputable def fourCenters : Finset (Option ℝ) := {some 0,some 1,some 2,some 3}

theorem fourCenters_coe : (fourCenters : Set (Option ℝ)) = fourDomain := by
  classical
  ext x; simp [fourCenters,fourDomain]

theorem fourCenters_card : fourCenters.card = 4 := by
  classical
  norm_num [fourCenters]
theorem four_nonempty : fourDomain.Nonempty := ⟨some 0,by simp [fourDomain]⟩
theorem four_finite : fourDomain.Finite := by rw [← fourCenters_coe]; exact Finset.finite_toSet _

theorem separated_finite_cover {A : Type} (d : A → A → ENNReal) (C : Finset A) (ε : ENNReal)
    (hε : 0 < ε) (hself : ∀ x, d x x = 0)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ε ≤ d x y) :
    covering_number d ε (C : Set A) = C.card := by
  apply le_antisymm
  · have hC : InternalEpsilonNet d ε (C : Set A) C := by
      exact ⟨Subset.rfl,fun x hx => ⟨x,hx,by simpa [hself] using hε⟩⟩
    exact iInf_le_of_le C (iInf_le_of_le hC le_rfl)
  · apply le_iInf; intro D
    apply le_iInf; intro hD
    have hsub : C ⊆ D := by
      intro x hx
      obtain ⟨y,hy,hxy⟩ := hD.2 x hx
      have he : x = y := by
        by_contra hn
        exact (not_lt_of_ge (hsep x hx y (hD.1 hy) hn)) hxy
      exact he ▸ hy
    exact_mod_cast Finset.card_le_card hsub

theorem four_separated {x y : Option ℝ} (hx : x ∈ fourDomain) (hy : y ∈ fourDomain) (hne : x ≠ y) :
    (1 : ENNReal) ≤ realDist x y := by
  rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
    rcases hx with rfl <;> rcases hy with rfl <;> norm_num [realDist_formula] at *

theorem four_cover_small {ε : ENNReal} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    covering_number realDist ε fourDomain = 4 := by
  rw [← fourCenters_coe]
  have he := separated_finite_cover realDist fourCenters ε hε realDist_lawful.dist_self (fun x hx y hy hne =>
    hε1.trans (four_separated (by simpa [← fourCenters_coe] using hx) (by simpa [← fourCenters_coe] using hy) hne))
  simpa [fourCenters_card] using he

theorem four_cover_le_two {ε : ENNReal} (hε : 1 < ε) : covering_number realDist ε fourDomain ≤ 2 := by
  classical
  let C : Finset (Option ℝ) := {some 1,some 2}
  have hC : InternalEpsilonNet realDist ε fourDomain C := by
    constructor
    · intro c hc
      change c ∈ C at hc
      simp only [C,Finset.mem_insert,Finset.mem_singleton] at hc
      rcases hc with rfl | rfl <;> simp [fourDomain]
    · intro x hx
      rcases hx with hx | hx | hx | hx <;> rcases hx with rfl
      · exact ⟨some 1,by simp [C],by convert hε using 1 <;> norm_num [realDist_formula]⟩
      · exact ⟨some 1,by simp [C],by simpa [realDist_formula] using zero_lt_one.trans hε⟩
      · exact ⟨some 2,by simp [C],by simpa [realDist_formula] using zero_lt_one.trans hε⟩
      · exact ⟨some 2,by simp [C],by convert hε using 1 <;> norm_num [realDist_formula]⟩
  exact iInf_le_of_le C (iInf_le_of_le hC (by norm_num [C]))

theorem four_cover_ge_two {ε : ENNReal} (hε : ε ≤ 2) : 2 ≤ covering_number realDist ε fourDomain := by
  apply le_iInf; intro C
  apply le_iInf; intro hC
  obtain ⟨a,ha,h0⟩ := hC.2 (some 0) (by simp [fourDomain])
  obtain ⟨b,hb,h3⟩ := hC.2 (some 3) (by simp [fourDomain])
  have hne : a ≠ b := by
    intro he
    subst b
    have h0' := h0.trans_le hε
    have h3' := h3.trans_le hε
    have hm := hC.1 ha
    rcases hm with hm | hm | hm | hm <;> rcases hm with rfl <;>
      first
      | (solve | norm_num [realDist_formula] at h0')
      | (solve | norm_num [realDist_formula] at h3')
  exact_mod_cast Nat.succ_le_of_lt (Finset.one_lt_card.mpr ⟨a,ha,b,hb,hne⟩)

theorem four_cover_medium {ε : ENNReal} (hε1 : 1 < ε) (hε2 : ε ≤ 2) :
    covering_number realDist ε fourDomain = 2 :=
  le_antisymm (four_cover_le_two hε1) (four_cover_ge_two hε2)

theorem four_cover_large {ε : ENNReal} (hε : 2 < ε) : covering_number realDist ε fourDomain = 1 := by
  classical
  apply le_antisymm
  · have hC : InternalEpsilonNet realDist ε fourDomain {some 1} := by
      constructor
      · intro x hx
        have he : x = some 1 := Finset.mem_singleton.mp hx
        subst x; simp [fourDomain]
      · intro x hx
        refine ⟨some 1,by simp,?_⟩
        apply lt_of_le_of_lt _ hε
        rcases hx with hx | hx | hx | hx <;> rcases hx with rfl <;> norm_num [realDist_formula]
    exact iInf_le_of_le {some 1} (iInf_le_of_le hC (by simp))
  · exact one_le_covering_number_of_nonempty _ _ _ four_nonempty

theorem four_cover_all {ε : ENNReal} (hε : 0 < ε) :
    covering_number realDist ε fourDomain = if ε ≤ 1 then 4 else if ε ≤ 2 then 2 else 1 := by
  split_ifs with h1 h2
  · exact four_cover_small hε h1
  · exact four_cover_medium (lt_of_not_ge h1) h2
  · exact four_cover_large (lt_of_not_ge h2)

theorem three_halves_not_internal : some (3/2 : ℝ) ∉ fourDomain := by norm_num [fourDomain]

noncomputable def fourIdentity : Operator (Option ℝ) none := by
  classical
  exact ⟨fun x => if x ∈ fourDomain then x else none,by simp [fourDomain]⟩
noncomputable def fourShuffle : Operator (Option ℝ) none :=
  ⟨fun z => match z with
    | none => none
    | some x => if x = 0 then some 0 else if x = 1 then some 3 else
      if x = 2 then some 1 else if x = 3 then some 2 else none,rfl⟩

theorem fourIdentity_on_domain {x : Option ℝ} (hx : x ∈ fourDomain) : fourIdentity.func x = x := by
  simp [fourIdentity,hx]

theorem four_operators_domains : dom fourIdentity = fourDomain ∧ dom fourShuffle = fourDomain := by
  constructor
  · ext x
    by_cases hx : x ∈ fourDomain
    · have hnone : x ≠ none := by rcases hx with hx | hx | hx | hx <;> rcases hx with rfl <;> simp
      simp [dom,fourIdentity,hx,hnone]
    · simp [dom,fourIdentity,hx]
  · ext x
    cases x with
    | none => simp [dom,fourShuffle,fourDomain]
    | some r =>
      by_cases h0 : r = 0 <;> by_cases h1 : r = 1 <;> by_cases h2 : r = 2 <;> by_cases h3 : r = 3 <;>
        simp_all [dom,fourShuffle,fourDomain]

theorem four_images : fourIdentity.func '' fourDomain = fourDomain ∧ fourShuffle.func '' fourDomain = fourDomain := by
  constructor
  · ext x
    constructor
    · rintro ⟨y,hy,he⟩
      rw [fourIdentity_on_domain hy] at he
      exact he ▸ hy
    · intro hx
      exact ⟨x,hx,fourIdentity_on_domain hx⟩
  · simp [fourDomain,Set.image_insert_eq,Set.image_singleton,fourShuffle]
    ext x; simp; tauto

theorem same_image_entropy_difference {A : Type} (d : A → A → ENNReal) (f : A → A)
    (U : Set A) (hU : U.Finite) (hn : U.Nonempty) (hself : ∀ x, d x x = 0)
    (him : f '' U = U) {ε : ENNReal} (hε : 0 < ε) :
    ∃ h : DifferenceDefined d d f U ε, EntropyDifference d d f U ε h = 0 := by
  have hc := finite_entropy_real hself hU hn hε
  obtain ⟨r,hr⟩ := hc.2.2
  refine ⟨Or.inl hc.2.1,?_⟩
  simp [EntropyDifference,him,hr]

theorem four_image_covers_and_differences {ε : ENNReal} (hε : 0 < ε) :
    covering_number realDist ε (fourIdentity.func '' fourDomain) = covering_number realDist ε fourDomain ∧
    covering_number realDist ε (fourShuffle.func '' fourDomain) = covering_number realDist ε fourDomain ∧
    (∃ h : DifferenceDefined realDist realDist fourIdentity.func fourDomain ε,
      EntropyDifference realDist realDist fourIdentity.func fourDomain ε h = 0) ∧
    (∃ h : DifferenceDefined realDist realDist fourShuffle.func fourDomain ε,
      EntropyDifference realDist realDist fourShuffle.func fourDomain ε h = 0) := by
  exact ⟨by rw [four_images.1],by rw [four_images.2],
    same_image_entropy_difference realDist _ _ four_finite four_nonempty realDist_lawful.dist_self four_images.1 hε,
    same_image_entropy_difference realDist _ _ four_finite four_nonempty realDist_lawful.dist_self four_images.2 hε⟩

theorem four_identity_lip :
    (∀ x ∈ fourDomain, ∀ y ∈ fourDomain, realDist (fourIdentity.func x) (fourIdentity.func y) ≤ 1 * realDist x y) ∧
    (∀ L : ENNReal, (∀ x ∈ fourDomain, ∀ y ∈ fourDomain,
      realDist (fourIdentity.func x) (fourIdentity.func y) ≤ L * realDist x y) → 1 ≤ L) := by
  constructor
  · intro x hx y hy; simp [fourIdentity_on_domain hx,fourIdentity_on_domain hy]
  · intro L hL
    have h := hL (some 0) (by simp [fourDomain]) (some 1) (by simp [fourDomain])
    simpa [fourIdentity,fourDomain,realDist_formula] using h

theorem four_shuffle_lip :
    (∀ x ∈ fourDomain, ∀ y ∈ fourDomain, realDist (fourShuffle.func x) (fourShuffle.func y) ≤ 3 * realDist x y) ∧
    (∀ L : ENNReal, (∀ x ∈ fourDomain, ∀ y ∈ fourDomain,
      realDist (fourShuffle.func x) (fourShuffle.func y) ≤ L * realDist x y) → 3 ≤ L) := by
  constructor
  · intro x hx y hy
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
      rcases hx with rfl <;> rcases hy with rfl <;>
        norm_num [fourShuffle,realDist,readingDist,absorbDist,edist_dist,Real.dist_eq]
  · intro L hL
    have h := hL (some 0) (by simp [fourDomain]) (some 1) (by simp [fourDomain])
    simpa [fourShuffle,realDist,readingDist,absorbDist,edist_dist,Real.dist_eq] using h

theorem four_precision_comparison :
    covering_number realDist (7/4) (fourIdentity.func '' fourDomain) = 2 ∧
    covering_number realDist (7/4) (fourShuffle.func '' fourDomain) = 2 ∧
    covering_number realDist ((7/4)/1) fourDomain = 2 ∧
    covering_number realDist ((7/4)/3) fourDomain = 4 ∧
    covering_number realDist (7/4) (fourIdentity.func '' fourDomain) ≤ covering_number realDist ((7/4)/1) fourDomain ∧
    covering_number realDist (7/4) (fourShuffle.func '' fourDomain) ≤ covering_number realDist ((7/4)/3) fourDomain := by
  have hε1 : (1 : ENNReal) < 7/4 := by norm_num [ENNReal.lt_div_iff_mul_lt]
  have hε2 : (7/4 : ENNReal) ≤ 2 := by norm_num [ENNReal.div_le_iff]
  have hc : covering_number realDist (7/4) fourDomain = 2 := four_cover_medium hε1 hε2
  have hsmall : ((7/4)/3 : ENNReal) ≤ 1 := by norm_num [ENNReal.div_le_iff]
  have hpos : (0 : ENNReal) < (7/4)/3 :=
    ENNReal.div_pos (ne_of_gt (zero_lt_one.trans hε1)) (by norm_num)
  exact ⟨by rw [four_images.1,hc],by rw [four_images.2,hc],by simpa using hc,
    four_cover_small hpos hsmall,
    (lip_transfer (by norm_num : (0 : ENNReal) < 1) (by norm_num : (1 : ENNReal) < ⊤) four_identity_lip.1 (7/4)).2,
    (lip_transfer (by norm_num : (0 : ENNReal) < 3) (by norm_num : (3 : ENNReal) < ⊤) four_shuffle_lip.1 (7/4)).2⟩

theorem translationDomain_image {A : Type} (h : Option ℝ → A) :
    h '' translationDomain = {h (some (-3)),h (some (-2)),h (some 0),h (some 2)} := by
  simp [translationDomain,Set.image_insert_eq,Set.image_singleton]

theorem translation_partition_equalities :
    (Fiber (fun _ : Unit => absDist) id translationDomain {()}) '' (id '' translationDomain) =
      {{some (-3)},{some (-2),some 2},{some 0}} ∧
    (Fiber (fun _ : Unit => absDist) translation.func translationDomain {()}) ''
      (translation.func '' translationDomain) = {{some (-3)},{some (-2),some 0},{some 2}} := by
  constructor
  · rw [Set.image_id,translationDomain_image]
    rw [identity_translation_domain_fibers.1,identity_translation_domain_fibers.2.1,
      identity_translation_domain_fibers.2.2.1,identity_translation_domain_fibers.2.2.2]
    ext F; simp <;> tauto
  · rw [Set.image_image,translationDomain_image]
    rw [translation_fibers.1,translation_fibers.2.1,translation_fibers.2.2.1,translation_fibers.2.2.2]
    ext F; simp <;> tauto
end Supplement

/- Explicit bridge from a matrix row to each scalar co-Lip entry. -/
theorem matrix_entry_lower {d : I → X → X → ENNReal} {f : X → X} {U : Set X}
    (K : I → ENNReal) (j : I)
    (hK : ∀ x ∈ U, ∀ y ∈ U, (∑' k, K k * d k x y) ≤ d j (f x) (f y)) (i : I) :
    ∀ x ∈ U, ∀ y ∈ U, K i * d i x y ≤ d j (f x) (f y) := by
  intro x hx y hy
  exact (ENNReal.le_tsum i).trans (hK x hx y hy)

theorem matrix_colip_gap_point {d : I → X → X → ENNReal} {f : X → X} {U : Set X}
    (K : I → ENNReal) (i j : I) (hpos : 0 < K i)
    (hK : ∀ x ∈ U, ∀ y ∈ U, (∑' k, K k * d k x y) ≤ d j (f x) (f y))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    ¬ (0 < d i x y ∧ d i x y < Radius (d i) (d j) f U y) :=
  colip_gap_point hpos (matrix_entry_lower K j hK i) hx hy

theorem matrix_colip_gap_uniform {d : I → X → X → ENNReal} {f : X → X} {U : Set X}
    (K : I → ENNReal) (i j : I) (hpos : 0 < K i)
    (hK : ∀ x ∈ U, ∀ y ∈ U, (∑' k, K k * d k x y) ≤ d j (f x) (f y))
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ Uniform (d i) (d j) f U ≤ d i x y :=
  colip_gap_uniform hpos (matrix_entry_lower K j hK i) hx hy
end Chapter3
```

```lean filename=Audit.lean
import Main
#print axioms Chapter3.Const
#print axioms Chapter3.Fixed
#print axioms Chapter3.Ident
#print axioms Chapter3.Active
#print axioms Chapter3.component_partition
#print axioms Chapter3.Fiber
#print axioms Chapter3.composite_zero
#print axioms Chapter3.fiber_representation
#print axioms Chapter3.EqRel
#print axioms Chapter3.ZeroRel
#print axioms Chapter3.FiberPreorder
#print axioms Chapter3.fiber_preorder_refl
#print axioms Chapter3.fiber_preorder_trans
#print axioms Chapter3.zero_trans
#print axioms Chapter3.zero_replace
#print axioms Chapter3.fixed_isometry
#print axioms Chapter3.ident_isometry
#print axioms Chapter3.outer_const
#print axioms Chapter3.ident_comp
#print axioms Chapter3.active_comp
#print axioms Chapter3.identity_not_active
#print axioms Chapter3.const_zero_row
#print axioms Chapter3.const_colip_entry
#print axioms Chapter3.fiber_target_zero
#print axioms Chapter3.fiber_image_nonempty
#print axioms Chapter3.fiber_cover
#print axioms Chapter3.fibers_equal_or_disjoint
#print axioms Chapter3.fiber_intersection
#print axioms Chapter3.fiber_antitone
#print axioms Chapter3.fiber_singleton
#print axioms Chapter3.fiber_full_subset
#print axioms Chapter3.fiber_ident
#print axioms Chapter3.fiber_const
#print axioms Chapter3.fiber_const_empty
#print axioms Chapter3.Factors
#print axioms Chapter3.factors_iff
#print axioms Chapter3.mutual_factors_iff
#print axioms Chapter3.Legal
#print axioms Chapter3.Radius
#print axioms Chapter3.UniformOn
#print axioms Chapter3.Uniform
#print axioms Chapter3.NullMatrix
#print axioms Chapter3.legal_ball_iff
#print axioms Chapter3.radius_empty_legal
#print axioms Chapter3.below_radius
#print axioms Chapter3.radius_mono_domain
#print axioms Chapter3.uniform_le_radius
#print axioms Chapter3.uniform_mono_domain
#print axioms Chapter3.below_uniform
#print axioms Chapter3.separated_lower_bound
#print axioms Chapter3.threshold_ball
#print axioms Chapter3.const_radius
#print axioms Chapter3.const_uniform
#print axioms Chapter3.identity_radius_bound
#print axioms Chapter3.composite_radius_mono
#print axioms Chapter3.radius_output_antitone
#print axioms Chapter3.uniform_output_antitone
#print axioms Chapter3.ScaleFamily
#print axioms Chapter3.diameter
#print axioms Chapter3.diameter_mono
#print axioms Chapter3.diameterScale
#print axioms Chapter3.thresholdType
#print axioms Chapter3.threshold_type_iff
#print axioms Chapter3.threshold_exhaustive
#print axioms Chapter3.scale_threshold_mono
#print axioms Chapter3.radius_threshold_antitone
#print axioms Chapter3.scale_domain_mono
#print axioms Chapter3.small_domain_iff
#print axioms Chapter3.colip_gap_point
#print axioms Chapter3.colip_gap_uniform
#print axioms Chapter3.le_radius_iff
#print axioms Chapter3.radius_components
#print axioms Chapter3.uniform_components
#print axioms Chapter3.fiber_step
#print axioms Chapter3.radius_step
#print axioms Chapter3.composite_fiber_step
#print axioms Chapter3.identity_image_fiber
#print axioms Chapter3.const_family_radii
#print axioms Chapter3.chainPrefix
#print axioms Chapter3.chainPrefix_domain_step
#print axioms Chapter3.active_chain
#print axioms Chapter3.relation_chain
#print axioms Chapter3.relation_chain_strict
#print axioms Chapter3.imageSetoid
#print axioms Chapter3.ImageQuotient
#print axioms Chapter3.imageClass
#print axioms Chapter3.QuotientFactors
#print axioms Chapter3.quotient_factors_iff
#print axioms Chapter3.mutual_quotient_factors_iff
#print axioms Chapter3.separated_relations
#print axioms Chapter3.separated_factorization
#print axioms Chapter3.zero_relation_fiber
#print axioms Chapter3.insufficient_radius_witness
#print axioms Chapter3.transfer_net
#print axioms Chapter3.transfer_cover
#print axioms Chapter3.null_cover_bound
#print axioms Chapter3.const_cover_one
#print axioms Chapter3.const_entropy_zero
#print axioms Chapter3.TotallyBoundedBy
#print axioms Chapter3.totally_bounded_iff
#print axioms Chapter3.finite_cover_bound
#print axioms Chapter3.finite_entropy_real
#print axioms Chapter3.DifferenceDefined
#print axioms Chapter3.EntropyDifference
#print axioms Chapter3.entropy_difference_formula
#print axioms Chapter3.finite_difference_defined
#print axioms Chapter3.const_difference
#print axioms Chapter3.log2_mono_positive
#print axioms Chapter3.entropy_cover_mono
#print axioms Chapter3.null_entropy_bound
#print axioms Chapter3.pull_net
#print axioms Chapter3.pull_cover
#print axioms Chapter3.ident_cover_entropy
#print axioms Chapter3.entropy_finite_iff
#print axioms Chapter3.difference_no_indeterminate
#print axioms Chapter3.difference_top
#print axioms Chapter3.difference_bottom
#print axioms Chapter3.difference_real
#print axioms Chapter3.ident_difference_zero
#print axioms Chapter3.lip_transfer
#print axioms Chapter3.colip_transfer
#print axioms Chapter3.composite_lip_radius
#print axioms Chapter3.sparse_row_const
#print axioms Chapter3.factor_lip
#print axioms Chapter3.lip_entropy_bound
#print axioms Chapter3.colip_entropy_bound
#print axioms Chapter3.finite_difference_real
#print axioms Chapter3.Examples.twoDist
#print axioms Chapter3.Examples.twoDist_lawful
#print axioms Chapter3.Examples.swap
#print axioms Chapter3.Examples.twoDomain
#print axioms Chapter3.Examples.mem_twoDomain
#print axioms Chapter3.Examples.swap_domain
#print axioms Chapter3.Examples.swap_image
#print axioms Chapter3.Examples.swap_twice
#print axioms Chapter3.Examples.swap_active
#print axioms Chapter3.Examples.id_ident
#print axioms Chapter3.Examples.swap_counterexample
#print axioms Chapter3.Examples.infiniteDist
#print axioms Chapter3.Examples.infiniteDist_lawful
#print axioms Chapter3.Examples.identityOp
#print axioms Chapter3.Examples.twoGauge
#print axioms Chapter3.Examples.twoGauge_lawful
#print axioms Chapter3.Examples.identity_domain
#print axioms Chapter3.Examples.infinite_input_radius
#print axioms Chapter3.Examples.infinite_input_uniform
#print axioms Chapter3.Examples.identity_not_const
#print axioms Chapter3.Examples.infinite_radius_counterexample
#print axioms Chapter3.finite_inf_attained
#print axioms Chapter3.radius_component_minimum
#print axioms Chapter3.uniform_component_minimum
#print axioms Chapter3.point_constant_selfcomp
#print axioms Chapter3.ChannelType
#print axioms Chapter3.channel_type_formula
#print axioms Chapter3.Examples.swap_composite_domain
#print axioms Chapter3.Supplement.absorbDist
#print axioms Chapter3.Supplement.absorbDist_lawful
#print axioms Chapter3.Supplement.readingDist
#print axioms Chapter3.Supplement.readingDist_lawful
#print axioms Chapter3.Supplement.absDist
#print axioms Chapter3.Supplement.realDist
#print axioms Chapter3.Supplement.absDist_formula
#print axioms Chapter3.Supplement.realDist_formula
#print axioms Chapter3.Supplement.absDist_lawful
#print axioms Chapter3.Supplement.realDist_lawful
#print axioms Chapter3.Supplement.affine
#print axioms Chapter3.Supplement.zeroOne
#print axioms Chapter3.Supplement.affine_domain
#print axioms Chapter3.Supplement.affine_constant
#print axioms Chapter3.Supplement.affine_fiber
#print axioms Chapter3.Supplement.affine_component
#print axioms Chapter3.Supplement.affine_squared_fiber
#print axioms Chapter3.Supplement.affine_squared_component
#print axioms Chapter3.Supplement.discreteRead
#print axioms Chapter3.Supplement.discreteRead_lawful
#print axioms Chapter3.Supplement.Six
#print axioms Chapter3.Supplement.collapsedRead
#print axioms Chapter3.Supplement.sevenGauge
#print axioms Chapter3.Supplement.sevenGauge_lawful
#print axioms Chapter3.Supplement.sevenInner
#print axioms Chapter3.Supplement.sevenOuter
#print axioms Chapter3.Supplement.sevenDomain
#print axioms Chapter3.Supplement.seven_domain_legal
#print axioms Chapter3.Supplement.seven_image
#print axioms Chapter3.Supplement.seven_inner_constant
#print axioms Chapter3.Supplement.seven_composite_not_constant
#print axioms Chapter3.Supplement.seven_other_component_separates
#print axioms Chapter3.Supplement.realIdentity
#print axioms Chapter3.Supplement.real_two_point_scale_counterexample
#print axioms Chapter3.Supplement.translation
#print axioms Chapter3.Supplement.translationDomain
#print axioms Chapter3.Supplement.translation_domain
#print axioms Chapter3.Supplement.singleton_fiber_insert
#print axioms Chapter3.Supplement.singleton_domain_fiber
#print axioms Chapter3.Supplement.identity_translation_domain_fibers
#print axioms Chapter3.Supplement.translation_fibers
#print axioms Chapter3.Supplement.translation_input_cover
#print axioms Chapter3.Supplement.translation_output_cover
#print axioms Chapter3.Supplement.translation_entropy_difference
#print axioms Chapter3.Supplement.stepOp
#print axioms Chapter3.Supplement.stepDomain
#print axioms Chapter3.Supplement.step_domain_legal
#print axioms Chapter3.Supplement.step_formula
#print axioms Chapter3.Supplement.diameter_pair
#print axioms Chapter3.Supplement.floorOp
#print axioms Chapter3.Supplement.zeroTwo
#print axioms Chapter3.Supplement.floor_domain
#print axioms Chapter3.Supplement.zeroTwo_domain
#print axioms Chapter3.Supplement.zeroTwo_diameter
#print axioms Chapter3.Supplement.zeroTwo_floor_radius
#print axioms Chapter3.Supplement.zeroTwo_floor_uniform
#print axioms Chapter3.Supplement.zeroTwo_floor_type
#print axioms Chapter3.Supplement.floor_positive_radius_not_constant
#print axioms Chapter3.Supplement.realInterval
#print axioms Chapter3.Supplement.realInterval_diameter
#print axioms Chapter3.Supplement.realInterval_nonempty
#print axioms Chapter3.Supplement.floor_half_constant
#print axioms Chapter3.Supplement.floor_half_data
#print axioms Chapter3.Supplement.floor_crossing_radius_zero
#print axioms Chapter3.Supplement.floor_crossing_uniform_zero
#print axioms Chapter3.Supplement.floor_crossing_data
#print axioms Chapter3.Supplement.floor_wide_uniform_zero
#print axioms Chapter3.Supplement.floor_wide_data
#print axioms Chapter3.Supplement.step_real_nonzero
#print axioms Chapter3.Supplement.step_lower_radius
#print axioms Chapter3.Supplement.step_point_radius
#print axioms Chapter3.Supplement.legal_iff_radius_bound
#print axioms Chapter3.Supplement.step_legal_radii
#print axioms Chapter3.Supplement.step_point_radius_positive
#print axioms Chapter3.Supplement.step_uniform_zero
#print axioms Chapter3.Supplement.zeroOne_cover_half
#print axioms Chapter3.Supplement.step_cover_counterexample
#print axioms Chapter3.Supplement.fourDomain
#print axioms Chapter3.Supplement.fourCenters
#print axioms Chapter3.Supplement.fourCenters_coe
#print axioms Chapter3.Supplement.fourCenters_card
#print axioms Chapter3.Supplement.four_nonempty
#print axioms Chapter3.Supplement.four_finite
#print axioms Chapter3.Supplement.separated_finite_cover
#print axioms Chapter3.Supplement.four_separated
#print axioms Chapter3.Supplement.four_cover_small
#print axioms Chapter3.Supplement.four_cover_le_two
#print axioms Chapter3.Supplement.four_cover_ge_two
#print axioms Chapter3.Supplement.four_cover_medium
#print axioms Chapter3.Supplement.four_cover_large
#print axioms Chapter3.Supplement.four_cover_all
#print axioms Chapter3.Supplement.three_halves_not_internal
#print axioms Chapter3.Supplement.fourIdentity
#print axioms Chapter3.Supplement.fourShuffle
#print axioms Chapter3.Supplement.fourIdentity_on_domain
#print axioms Chapter3.Supplement.four_operators_domains
#print axioms Chapter3.Supplement.four_images
#print axioms Chapter3.Supplement.same_image_entropy_difference
#print axioms Chapter3.Supplement.four_image_covers_and_differences
#print axioms Chapter3.Supplement.four_identity_lip
#print axioms Chapter3.Supplement.four_shuffle_lip
#print axioms Chapter3.Supplement.four_precision_comparison
#print axioms Chapter3.Supplement.translationDomain_image
#print axioms Chapter3.Supplement.translation_partition_equalities
#print axioms Chapter3.matrix_entry_lower
#print axioms Chapter3.matrix_colip_gap_point
#print axioms Chapter3.matrix_colip_gap_uniform
#print axioms formal_oet.vol_01.ch_01_foundations.InternalEpsilonNet
#print axioms formal_oet.vol_01.ch_01_foundations.covering_number
#print axioms formal_oet.vol_01.ch_01_foundations.covering_number_attained
#print axioms formal_oet.vol_01.ch_01_foundations.covering_number_eq_top_iff
#print axioms formal_oet.vol_01.ch_01_foundations.log2_ereal
#print axioms formal_oet.vol_01.ch_01_foundations.metric_entropy
#print axioms formal_oet.vol_01.ch_01_foundations.subfamily_pseudometric
#print axioms formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy
#print axioms formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy_eq_metric_entropy
```

```json filename=alignment.json
{
  "case_id": "MG-C003",
  "version": "0.1.1",
  "items": [
    {
      "id": "CH03-D01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Const"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Fixed"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Ident"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Active"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.component_partition"
        }
      ],
      "representation": "Each index is represented by applying the predicates to d i. Ident explicitly excludes Const, so the three proved mutually exclusive and exhaustive predicates implement constant-first component partitioning.",
      "dependencies": []
    },
    {
      "id": "CH03-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Fiber"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.composite_zero"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_representation"
        }
      ],
      "representation": "Fiber is exactly the restricted set defined by zero composite output distance. composite_zero proves equivalence of the supremum composite pseudometric with all component zero equations.",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.EqRel"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.ZeroRel"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.FiberPreorder"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.imageSetoid"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.ImageQuotient"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.imageClass"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.zero_relation_fiber"
        }
      ],
      "representation": "Relations are subsets of X×X with both endpoints in U. The actual image subtype carries the componentwise zero setoid, whose equivalence is proved from pseudometric axioms; its quotient and canonical image class are constructed. The fiber relation correspondence includes symmetry.",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Legal"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Radius"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.legal_ball_iff"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.radius_empty_legal"
        }
      ],
      "representation": "Legal radii are ENNReal values strictly between zero and infinity. The ball-intersection inclusion is proved equivalent to Legal; Radius is their supremum, with empty legal set giving zero.",
      "dependencies": []
    },
    {
      "id": "CH03-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.UniformOn"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Uniform"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.NullMatrix"
        }
      ],
      "representation": "UniformOn distinguishes the basepoint set A from the assessment domain U; Uniform uses A=U. NullMatrix has arguments output j followed by input i and is the singleton-output uniform radius.",
      "dependencies": [
        "CH03-D04"
      ]
    },
    {
      "id": "CH03-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.ScaleFamily"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.diameter"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.diameter_mono"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.diameterScale"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.thresholdType"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.ChannelType"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.channel_type_formula"
        }
      ],
      "representation": "ScaleFamily is monotone on nonempty subsets. diameterScale proves validity of the default double supremum diameter. ChannelType uses the input scale and the j,i null-matrix entry, encoding 1 and 0 by true and false.",
      "dependencies": [
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-D07",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.TotallyBoundedBy"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.totally_bounded_iff"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.InternalEpsilonNet"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.covering_number"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.covering_number_attained"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.covering_number_eq_top_iff"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.log2_ereal"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.metric_entropy"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.subfamily_pseudometric"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy"
        },
        {
          "file": "formal_oet/vol_01/ch_01_foundations/metric_entropy.lean",
          "name": "formal_oet.vol_01.ch_01_foundations.subfamily_metric_entropy_eq_metric_entropy"
        }
      ],
      "representation": "The imported frozen InternalEpsilonNet uses finite centers inside the set and strict open balls. covering_number_attained and covering_number_eq_top_iff supply the minimum/infinity correspondence. Composite distance and entropy are the imported chapter-1 definitions. TotallyBoundedBy is proved equivalent to finite covering number at every finite positive precision.",
      "dependencies": []
    },
    {
      "id": "CH03-D08",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.DifferenceDefined"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.EntropyDifference"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.entropy_difference_formula"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.difference_no_indeterminate"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.difference_top"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.difference_bottom"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.difference_real"
        }
      ],
      "representation": "The difference requires the specified disjunction of finite input/output covering numbers. Instantiating di and dout by the respective composite pseudometrics gives the chapter definition. The no-infinity-minus-infinity condition, both infinite-result branches, and finite-real subtraction are proved.",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P01-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.const_zero_row"
        }
      ],
      "representation": "Constant output has zero ENNReal tsum upper row, for every pair in U.",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P01-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.const_colip_entry"
        }
      ],
      "representation": "An actual sum lower bound plus a positive source-distance witness forces the corresponding ENNReal coefficient to zero, including infinite distances and coefficients.",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P01-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.ident_isometry"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.zero_replace"
        }
      ],
      "representation": "Identity components preserve the component distance in both directions, using symmetry and triangle inequalities.",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P02-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.active_comp"
        }
      ],
      "representation": "Componentwise implication represents the requested set inclusion. The outer evaluation domain is exactly f image U. All constant/identity alternatives are handled.",
      "dependencies": [
        "CH03-D01",
        "CH03-P01-03",
        "CH03-P02-03",
        "CH03-P04-01"
      ]
    },
    {
      "id": "CH03-P02-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.chainPrefix"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.chainPrefix_domain_step"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.active_chain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.identity_not_active"
        }
      ],
      "representation": "chainPrefix uses zero-based steps, starts with id, and recurses by postcomposition. The intermediate domain is exactly the prefix image. The theorem gives a step k<n witnessing activity; the zero-step case is proved impossible.",
      "dependencies": [
        "CH03-P02-01",
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P02-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.ident_comp"
        }
      ],
      "representation": "Both pointwise zero-displacement and exclusion of constant output are proved for the composition on U and the actual intermediate image.",
      "dependencies": [
        "CH03-D01",
        "CH03-P01-03"
      ]
    },
    {
      "id": "CH03-P03-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.twoDist"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.twoDist_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.swap"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.twoDomain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.swap_domain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.swap_image"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.swap_twice"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.swap_composite_domain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.swap_counterexample"
        }
      ],
      "representation": "Option Bool realizes the absorbing point and the two exchanged points, with distance 1 between them. The extended metric and lawful operator/domain/image are checked. Both steps are active and nonidentity while the composition is identity and nonactive. With a singleton index set these are the stated component-set computations and witnesses against both reverse inclusions.",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P04-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.outer_const"
        }
      ],
      "representation": "Outer constancy on the actual image directly implies composite constancy on U.",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P04-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.Six"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.discreteRead"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.discreteRead_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.sevenGauge"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.sevenGauge_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.sevenInner"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.sevenOuter"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.sevenDomain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.seven_domain_legal"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.seven_image"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.seven_inner_constant"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.seven_composite_not_constant"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.seven_other_component_separates"
        }
      ],
      "representation": "Option Six has exactly the absorbing point and a,b,p,q,r,s. The first component identifies p,q and has unit distance on all other distinct nonabsorbing classes; the second is discrete. Both extended pseudometrics and both absorbing-point operators are proved lawful. The exact inner image is {p,q}; it is constant in the first component, while the composite outputs r,s at distance one. The second component separates p,q.",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P05-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.sparse_row_const"
        }
      ],
      "representation": "An actual output-row sum inequality on the image and zero off-diagonal coefficients propagate inner constancy. No coefficient finiteness assumption is imposed.",
      "dependencies": [
        "CH03-D01"
      ]
    },
    {
      "id": "CH03-P06-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_target_zero"
        }
      ],
      "representation": "Arbitrary targets with all selected component distances zero give identical restricted fibers, by triangle inequalities and symmetry.",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_image_nonempty"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_cover"
        }
      ],
      "representation": "Every image-target fiber is nonempty, and their union is exactly U, including U empty.",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.fibers_equal_or_disjoint"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_cover"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_image_nonempty"
        }
      ],
      "representation": "For any two targets, fibers are equal or disjoint; together with image-fiber nonemptiness and exact coverage this is the partition after duplicate removal.",
      "dependencies": [
        "CH03-D02",
        "CH03-P06-01",
        "CH03-P06-02"
      ]
    },
    {
      "id": "CH03-P06-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_intersection"
        }
      ],
      "representation": "For nonempty J, the fiber equals the intersection of singleton-component fibers. The proof works for arbitrary J, hence for finite nonempty J.",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-05",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_antitone"
        }
      ],
      "representation": "J subset K implies K-fiber subset J-fiber.",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P06-06",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_singleton"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_full_subset"
        }
      ],
      "representation": "Singleton fibers have exactly one zero-distance equation; the full-family fiber is contained in each singleton fiber.",
      "dependencies": [
        "CH03-D02",
        "CH03-P06-05"
      ]
    },
    {
      "id": "CH03-P06-07",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_ident"
        }
      ],
      "representation": "At an identity component, every arbitrary-target fiber equals the corresponding input zero-distance class within U.",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P06-06"
      ]
    },
    {
      "id": "CH03-P06-08",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_const"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_const_empty"
        }
      ],
      "representation": "Constant component fibers at image targets equal U. For arbitrary targets at positive distance from an image target, the fiber is empty.",
      "dependencies": [
        "CH03-D01",
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P07-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Factors"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.factors_iff"
        }
      ],
      "representation": "The forward implication of factors_iff proves actual point-valued image factorization implies inclusion of equality relations.",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P07-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Factors"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.factors_iff"
        }
      ],
      "representation": "The reverse implication constructs T on the image subtype using representatives and relation inclusion; it also works when U is empty.",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P07-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.mutual_factors_iff"
        }
      ],
      "representation": "Factorizations in both directions are equivalent to equality of the restricted point-value relations.",
      "dependencies": [
        "CH03-P07-01",
        "CH03-P07-02"
      ]
    },
    {
      "id": "CH03-P07-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.factor_lip"
        }
      ],
      "representation": "For a specified image factorization T, positive finite K and finite L give the exact L/K scalar inequality on all actual image points.",
      "dependencies": []
    },
    {
      "id": "CH03-P08-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.QuotientFactors"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.quotient_factors_iff"
        }
      ],
      "representation": "The quotient-lift construction is independent of image representatives, satisfies the required canonical-class equation, and is equivalent to zero-relation inclusion.",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P08-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.mutual_quotient_factors_iff"
        }
      ],
      "representation": "Factorizations between the two actual-image zero quotients in both directions are equivalent to equality of zero relations.",
      "dependencies": [
        "CH03-P08-01"
      ]
    },
    {
      "id": "CH03-P08-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.separated_relations"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.separated_factorization"
        }
      ],
      "representation": "Explicit separation is assumed only on each actual image. Under precisely those hypotheses the zero relations equal point-value equality relations, and the factorization criteria agree.",
      "dependencies": [
        "CH03-D03",
        "CH03-P07-01",
        "CH03-P07-02",
        "CH03-P08-01"
      ]
    },
    {
      "id": "CH03-P09-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_preorder_refl"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_preorder_trans"
        }
      ],
      "representation": "Fixed-domain inclusion of restricted zero relations is reflexive and transitive.",
      "dependencies": [
        "CH03-D03"
      ]
    },
    {
      "id": "CH03-P09-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.relation_chain"
        }
      ],
      "representation": "For any chain of sets R k and any a≤b≤n, consecutive inclusions imply R a subset R b. Instantiate R k with the restricted zero relations on the common U.",
      "dependencies": []
    },
    {
      "id": "CH03-P09-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.relation_chain_strict"
        }
      ],
      "representation": "A strict step supplies a concrete point-pair in the final relation but not the initial relation, as well as strict endpoint inclusion.",
      "dependencies": [
        "CH03-P09-02"
      ]
    },
    {
      "id": "CH03-P10-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.absorbDist"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.readingDist"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realDist"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realDist_formula"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realDist_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.stepOp"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.stepDomain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_domain_legal"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_formula"
        }
      ],
      "representation": "Option ℝ realizes the usual real line plus its isolated absorbing point. The exact usual-distance formula and all extended pseudometric axioms are proved. stepOp is the absorbing-preserving step 0 for x<0, 1 for x≥0. stepDomain is exactly the image of [-1,0) union (0,1], and is proved nonempty and contained in the operator domain.",
      "dependencies": []
    },
    {
      "id": "CH03-P10-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_real_nonzero"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_lower_radius"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_point_radius"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.legal_iff_radius_bound"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_legal_radii"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_point_radius_positive"
        }
      ],
      "representation": "For every real y in the fixed step domain, the point radius equals ofReal |y| and is positive. Legal finite positive radii are proved equivalent to 0<r≤ofReal |y|, including the endpoint r=|y|. The upper bound constructs an opposite-sign domain point whenever the proposed radius exceeds |y|.",
      "dependencies": [
        "CH03-D04",
        "CH03-P10-01",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P10-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_uniform_zero"
        }
      ],
      "representation": "On the same fixed stepDomain the uniform radius is exactly zero. For every positive extended threshold the proof constructs a positive basepoint inside this domain whose computed point radius lies below the threshold.",
      "dependencies": [
        "CH03-D05",
        "CH03-P10-02"
      ]
    },
    {
      "id": "CH03-P11-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_const"
        }
      ],
      "representation": "Constancy of every selected output component makes every image-target J-fiber equal U.",
      "dependencies": [
        "CH03-D01",
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P11-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.const_family_radii"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.const_radius"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.const_uniform"
        }
      ],
      "representation": "Constancy gives top pointwise radii at all basepoints and top uniform radius for any input distance. The proof uses arbitrarily large strictly positive finite legal radii.",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
        "CH03-D05",
        "CH03-D07",
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P11-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.infiniteDist_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.twoGauge_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.identityOp"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.identity_domain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.infinite_input_radius"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Examples.infinite_radius_counterexample"
        }
      ],
      "representation": "The lawful Option Bool structure with two components realizes infinite input separation and either infinite same-component or unit distinct-component output separation. Identity has top pointwise/uniform radii but is not constant in either output component.",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-P12-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.identity_image_fiber"
        }
      ],
      "representation": "For y in U, the identity-component fiber at f y is exactly the input zero class of y within U.",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P01-03",
        "CH03-P06-06"
      ]
    },
    {
      "id": "CH03-P12-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.identity_radius_bound"
        }
      ],
      "representation": "A finite positive radius whose input ball contains only zero-distance points is legal under the identity-component assumption, yielding radius≥r>0.",
      "dependencies": [
        "CH03-D01",
        "CH03-D04",
        "CH03-P01-03"
      ]
    },
    {
      "id": "CH03-P13-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.radius_components"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.finite_inf_attained"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.radius_component_minimum"
        }
      ],
      "representation": "The pointwise family radius equals the infimum of singleton radii. For a finite nonempty family, a minimizing component is explicitly obtained, proving the stated minimum formula.",
      "dependencies": [
        "CH03-D04",
        "CH03-D07",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P13-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.uniform_components"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.uniform_component_minimum"
        }
      ],
      "representation": "The basepoint and component infima are interchanged with both inequalities proved. The finite nonempty result is attained at a component and equals the corresponding null-matrix entry.",
      "dependencies": [
        "CH03-D05",
        "CH03-P13-01"
      ]
    },
    {
      "id": "CH03-P13-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.radius_output_antitone"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.uniform_output_antitone"
        }
      ],
      "representation": "Enlarging the selected output family decreases the pointwise and uniform radii.",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P14-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.fiber_step"
        }
      ],
      "representation": "A singleton-fiber membership gives output zero distance, with the chapter orientation obtained by symmetry.",
      "dependencies": [
        "CH03-D02"
      ]
    },
    {
      "id": "CH03-P14-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.below_radius"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.radius_step"
        }
      ],
      "representation": "Strict inequality below the supremum extracts a legal finite positive radius exceeding the distance and proves output zero distance. Both symmetry orientations are made explicit.",
      "dependencies": [
        "CH03-D04"
      ]
    },
    {
      "id": "CH03-P14-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.composite_fiber_step"
        }
      ],
      "representation": "Both inner image points are explicitly assumed in the downstream domain. Applying the singleton-fiber condition yields the composite output zero equation.",
      "dependencies": [
        "CH03-P14-01"
      ]
    },
    {
      "id": "CH03-P15-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.composite_radius_mono"
        }
      ],
      "representation": "A zero-preserving downstream map on the exact actual image sends every legal inner radius to a legal composite radius, proving the uniform lower bound.",
      "dependencies": [
        "CH03-D04",
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-P15-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.le_radius_iff"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.composite_lip_radius"
        }
      ],
      "representation": "The exact downstream uniform radius divided by L is a lower bound for the composite. The proof uses a characterization valid for all extended thresholds, including 0 and infinity, without excluding either boundary.",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-P14-02",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P16-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.threshold_type_iff"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.threshold_exhaustive"
        }
      ],
      "representation": "There exists exactly one Bool×Bool pair satisfying the two threshold comparisons. As Bool has exactly false/true this proves the four combinations exhaustive and mutually exclusive.",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P16-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.scale_threshold_mono"
        }
      ],
      "representation": "Increasing the scale threshold preserves every first-coordinate true comparison, pointwise on channels and hence as channel-set inclusion.",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P16-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.radius_threshold_antitone"
        }
      ],
      "representation": "Increasing the null-radius threshold can only shrink the second-coordinate true channel set.",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P17-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.scale_domain_mono"
        }
      ],
      "representation": "For every monotone scale family and nonempty B subset A, both the scale inequality and the strict threshold implication are proved.",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P17-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.radius_mono_domain"
        }
      ],
      "representation": "Shrinking the assessment domain enlarges the legal radius set at each fixed basepoint. The result holds even without requiring the basepoint in B, and therefore includes that case.",
      "dependencies": [
        "CH03-D04"
      ]
    },
    {
      "id": "CH03-P17-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.uniform_mono_domain"
        }
      ],
      "representation": "Both the assessment domain and the infimum basepoint domain shrink from A to B. Each basepoint comparison is composed with the original uniform lower bound.",
      "dependencies": [
        "CH03-D05",
        "CH03-P17-02"
      ]
    },
    {
      "id": "CH03-P17-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realDist_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realIdentity"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroOne"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.real_two_point_scale_counterexample"
        }
      ],
      "representation": "This is the actual absorbing real-line example, not merely an abstract two-point substitute. A={some 0,some 1}, B={some 0}, and the lawful identity operator satisfy the domain and nonemptiness conditions. Their diameters are 1 and 0, giving B<1/2 but not A<1/2.",
      "dependencies": [
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P18-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.below_uniform"
        }
      ],
      "representation": "Any input pair in the domain whose distance is strictly below the uniform radius has zero output distance.",
      "dependencies": [
        "CH03-D05",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P18-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.separated_lower_bound"
        }
      ],
      "representation": "Positive output distance forces the input distance to be at least the uniform radius, by contraposition.",
      "dependencies": [
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P18-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.insufficient_radius_witness"
        }
      ],
      "representation": "For every α strictly above the uniform radius, there are domain points with input distance below α and positive output separation. ε=min(output distance,1) is positive finite and bounded by the output distance, including infinite output separation.",
      "dependencies": [
        "CH03-D05",
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P19-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.threshold_ball"
        }
      ],
      "representation": "A threshold below or equal to the uniform radius makes every restricted open input ball lie in the corresponding output zero fiber.",
      "dependencies": [
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P19-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.transfer_net"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.transfer_cover"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.null_cover_bound"
        }
      ],
      "representation": "Images of finite internal input centers form internal output centers with nonincreasing cardinality. Infima give the bound for every B subset A, including empty B and absence of any finite input cover.",
      "dependencies": [
        "CH03-D07",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P19-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.log2_mono_positive"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.entropy_cover_mono"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.null_entropy_bound"
        }
      ],
      "representation": "The extended base-two logarithm is proved monotone on positive covering numbers. For nonempty B the covering bound therefore yields the stated entropy comparison, including infinite values.",
      "dependencies": [
        "CH03-D07",
        "CH03-P19-02"
      ]
    },
    {
      "id": "CH03-P20-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_domain_legal"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_point_radius_positive"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_uniform_zero"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroOne_cover_half"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.step_cover_counterexample"
        }
      ],
      "representation": "For every finite positive τ the theorem chooses a=min(τ.toReal/4,1)>0, proves a≤1 and ofReal(2a)<τ, and proves {-a,a} is inside the same fixed stepDomain. Its internal input covering number at τ is exactly one; its step image is {0,1}, whose internal covering number at 1/2 is exactly two.",
      "dependencies": [
        "CH03-D07",
        "CH03-P10-01",
        "CH03-P10-02",
        "CH03-P10-03"
      ]
    },
    {
      "id": "CH03-P21-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.small_domain_iff"
        }
      ],
      "representation": "Under diameter(A)<τσ≤τN, the τN uniform-radius test is equivalent to all outputs being zero-distance. Constancy gives top uniform radius for the reverse direction.",
      "dependencies": [
        "CH03-D01",
        "CH03-D05",
        "CH03-D06",
        "CH03-P11-02",
        "CH03-P18-01"
      ]
    },
    {
      "id": "CH03-P21-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.const_cover_one"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.small_domain_iff"
        }
      ],
      "representation": "For nonempty A and every positive ε, all-output zero distance makes a singleton internal output net, and nonemptiness supplies the matching lower bound one. Combining with small_domain_iff gives the requested consequence.",
      "dependencies": [
        "CH03-D07",
        "CH03-P21-01"
      ]
    },
    {
      "id": "CH03-P22-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.finite_cover_bound"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.finite_entropy_real"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.finite_difference_defined"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.finite_difference_real"
        }
      ],
      "representation": "Finite U is covered by its own centers. The theorem gives positive finite covering numbers and finite real entropy for each self-zero distance, hence for both composite metrics. The image of finite nonempty U is finite nonempty, and its entropy difference is a genuine real value.",
      "dependencies": [
        "CH03-D07",
        "CH03-D08"
      ]
    },
    {
      "id": "CH03-P23-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.const_cover_one"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.const_entropy_zero"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.const_difference"
        }
      ],
      "representation": "Constant components give output cover number one, entropy zero, and a defined entropy difference equal to the input entropy, with no finiteness assumption on that input entropy.",
      "dependencies": [
        "CH03-D01",
        "CH03-D07",
        "CH03-D08"
      ]
    },
    {
      "id": "CH03-P23-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.pull_net"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.pull_cover"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.ident_cover_entropy"
        }
      ],
      "representation": "Forward image centers and backward chosen representatives both give cardinality-nonincreasing internal nets. Identity-component isometry proves both covering inequalities and equality of entropy.",
      "dependencies": [
        "CH03-P01-03",
        "CH03-D07",
        "CH03-P19-02"
      ]
    },
    {
      "id": "CH03-P23-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.ident_difference_zero"
        }
      ],
      "representation": "Only under DifferenceDefined and nonempty U does equal entropy yield difference zero. Infinite input entropy is explicitly ruled out by the finiteness condition and equality of both entropies.",
      "dependencies": [
        "CH03-D08",
        "CH03-P23-02"
      ]
    },
    {
      "id": "CH03-P24-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.lip_transfer"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.transfer_net"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.transfer_cover"
        }
      ],
      "representation": "For positive finite L, an ε/L internal net pushes to an ε output net; the returned center set has cardinality at most the original, and the covering-number inequality follows.",
      "dependencies": [
        "CH03-D07",
        "CH03-P19-02"
      ]
    },
    {
      "id": "CH03-P24-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.lip_entropy_bound"
        }
      ],
      "representation": "Total boundedness makes the ε and ε/L input coverings finite, hence the ε output covering finite. Nonempty-set entropy is nonnegative and not top. The displayed entropy-difference lower bound follows with a proof of DifferenceDefined.",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P19-03",
        "CH03-P24-01"
      ]
    },
    {
      "id": "CH03-P25-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.colip_transfer"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.pull_net"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.pull_cover"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.matrix_entry_lower"
        }
      ],
      "representation": "For positive finite K, chosen preimages of each internal output center give an ε/K input net with no larger cardinality; the covering lower bound follows.",
      "dependencies": [
        "CH03-D07",
        "CH03-P23-02"
      ]
    },
    {
      "id": "CH03-P25-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.colip_entropy_bound"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.matrix_entry_lower"
        }
      ],
      "representation": "Input total boundedness supplies the finiteness condition for the entropy difference. The exact difference upper bound follows from the co-Lip covering inequality, without assuming output entropy finite.",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P19-03",
        "CH03-P25-01"
      ]
    },
    {
      "id": "CH03-P26-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.absDist"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.absDist_formula"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.absDist_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.affine"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroOne"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.affine_domain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.affine_constant"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.affine_fiber"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.affine_component"
        }
      ],
      "representation": "The actual Option ℝ model uses the absolute-value reading pseudometric ||x|-|y||, whose extended axioms are verified. The lawful affine map is 2x-1 on reals. On the exact U={0,1}, its fiber at φ(0) equals U and the component is constant, explicitly not identity and not active.",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P11-01"
      ]
    },
    {
      "id": "CH03-P26-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.affine_domain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.affine_squared_fiber"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.affine_squared_component"
        }
      ],
      "representation": "For the same U={0,1}, the selfcomposite has fiber {0} at φ²(0), and is active. The exact composite domain includes U; the proof does not replace U by an intermediate image.",
      "dependencies": [
        "CH03-D01",
        "CH03-D02",
        "CH03-P26-01"
      ]
    },
    {
      "id": "CH03-P26-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.point_constant_selfcomp"
        }
      ],
      "representation": "For any lawful absorbing-point operator, a common point-value c on U remains a common point-value f(c) after selfcomposition. If f(c) is nonabsorbing U stays in the composite domain; if it is absorbing the intersection with that domain is empty. This applies in particular to the real-valued constant case of the exercise.",
      "dependencies": []
    },
    {
      "id": "CH03-P27-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.colip_gap_point"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.matrix_entry_lower"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.matrix_colip_gap_point"
        }
      ],
      "representation": "Positive co-Lip coefficient and a pointwise null-radius test exclude every input distance in (0,radius); K is allowed to be infinite.",
      "dependencies": [
        "CH03-P14-02"
      ]
    },
    {
      "id": "CH03-P27-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.colip_gap_uniform"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.matrix_colip_gap_uniform"
        }
      ],
      "representation": "Each input pair has either zero distance or distance at least the uniform radius. The result is stronger than the positive-uniform-radius case, and K need not be finite.",
      "dependencies": [
        "CH03-P27-01",
        "CH03-D05"
      ]
    },
    {
      "id": "CH03-P28-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.absDist_formula"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.absDist_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realIdentity"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.translation"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.translationDomain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.translation_domain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.identity_translation_domain_fibers"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.translation_fibers"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.translation_partition_equalities"
        }
      ],
      "representation": "Both operators are lawful on the specified four-point real domain. The duplicate-free identity fiber partition is {{-3},{-2,2},{0}} and the translation fiber partition is {{-3},{-2,0},{2}}. Four target computations for each map and exact set-of-fibers equalities establish the complete partitions.",
      "dependencies": [
        "CH03-D02",
        "CH03-P26-01"
      ]
    },
    {
      "id": "CH03-P28-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.translation_input_cover"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.translation_output_cover"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.translation_entropy_difference"
        }
      ],
      "representation": "At the exact ENNReal precision 3/2, the internal input covering number is two and the internal output covering number is one. Explicit internal nets and lower bounds prove equality, and the defined extended-real entropy difference is exactly one.",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P28-01"
      ]
    },
    {
      "id": "CH03-P29-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realDist_formula"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realDist_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floorOp"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floor_domain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realInterval"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realInterval_nonempty"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realInterval_diameter"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floor_half_constant"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floor_half_data"
        }
      ],
      "representation": "The lawful absorbing real-line floor operator is restricted to the exact lifted closed interval [0,1/2]. Its diameter is ofReal(1/2), its uniform radius is infinity, and its threshold type at (1,1) is (true,true), representing (1,1).",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P11-02"
      ]
    },
    {
      "id": "CH03-P29-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floorOp"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floor_domain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realInterval_nonempty"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realInterval_diameter"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floor_crossing_radius_zero"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floor_crossing_uniform_zero"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floor_crossing_data"
        }
      ],
      "representation": "On the exact interval [9/10,11/10], diameter is ofReal(1/5), uniform radius is zero, and type is (true,false). At basepoint 1, every positive finite legal radius is contradicted by a point just below 1 inside the same interval.",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-D06",
        "CH03-P29-01"
      ]
    },
    {
      "id": "CH03-P29-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floorOp"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realDist_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroTwo"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroTwo_domain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroTwo_diameter"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroTwo_floor_radius"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroTwo_floor_uniform"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroTwo_floor_type"
        }
      ],
      "representation": "On the exact two-point domain {0,2}, diameter is two, each point radius and the uniform radius are two, and the threshold type is (false,true). The radius upper bound uses the other point, and the lower bound verifies every strict input ball.",
      "dependencies": [
        "CH03-D04",
        "CH03-D05",
        "CH03-D06"
      ]
    },
    {
      "id": "CH03-P29-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floorOp"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floor_domain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realInterval_nonempty"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realInterval_diameter"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floor_wide_uniform_zero"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floor_wide_data"
        }
      ],
      "representation": "On [0,2], diameter is two, uniform radius is zero, and type is (false,false). The crossing interval is explicitly included in this domain, so domain monotonicity transports its zero uniform-radius upper bound.",
      "dependencies": [
        "CH03-D05",
        "CH03-D06",
        "CH03-P17-03",
        "CH03-P29-02"
      ]
    },
    {
      "id": "CH03-P29-05",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroTwo_domain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroTwo_floor_radius"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.zeroTwo_floor_uniform"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.floor_positive_radius_not_constant"
        }
      ],
      "representation": "The lawful nonempty domain {0,2} has uniform radius two, hence at least one, but output distances are not all zero. The point-radius proof shows the positive radius comes from the isolated two-point input gap, not from constant output.",
      "dependencies": [
        "CH03-P29-03"
      ]
    },
    {
      "id": "CH03-P30-01",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.realDist_lawful"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.fourDomain"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.fourCenters"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.fourCenters_coe"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.fourCenters_card"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_nonempty"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_finite"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.separated_finite_cover"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_separated"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_cover_small"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_cover_medium"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_cover_large"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_cover_all"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.three_halves_not_internal"
        }
      ],
      "representation": "For every positive ε, the exact internal covering number is 4 for ε≤1, 2 for 1<ε≤2, and 1 for 2<ε. Thus the strict-ball endpoints at 1 and 2 are included in the correct branches. Finite-center lower bounds and explicit internal nets prove all branches. The proposed center 3/2 is proved outside U and therefore illegal at 7/4.",
      "dependencies": [
        "CH03-D07"
      ]
    },
    {
      "id": "CH03-P30-02",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.fourIdentity"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.fourShuffle"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_operators_domains"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_images"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.same_image_entropy_difference"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_image_covers_and_differences"
        }
      ],
      "representation": "Both absorbing-preserving operators have exactly U as domain, hence are absorbing outside U. Their actual images both equal U. Covering numbers at every positive precision coincide with the full piecewise formula, and both entropy differences are defined and equal zero.",
      "dependencies": [
        "CH03-D07",
        "CH03-D08",
        "CH03-P30-01"
      ]
    },
    {
      "id": "CH03-P30-03",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_identity_lip"
        },
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_shuffle_lip"
        }
      ],
      "representation": "The operators satisfy scalar Lip bounds one and three respectively on every pair in U. Evaluating the pair (0,1) proves the necessary lower bounds for every admissible ENNReal coefficient, establishing optimality.",
      "dependencies": [
        "CH03-P30-02"
      ]
    },
    {
      "id": "CH03-P30-04",
      "status": "complete",
      "declarations": [
        {
          "file": "Main.lean",
          "name": "Chapter3.Supplement.four_precision_comparison"
        }
      ],
      "representation": "At ε=7/4 both actual output covering numbers equal two. Applying the general Lip transfer bound with the proved optimal constants yields input covering numbers two at (7/4)/1 and four at (7/4)/3. Both inequalities and the exact comparison values are included.",
      "dependencies": [
        "CH03-P24-01",
        "CH03-P30-01",
        "CH03-P30-02",
        "CH03-P30-03"
      ]
    }
  ]
}
```

