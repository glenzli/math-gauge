未能完成整章的 92 项义务，因此不能将本答卷标为完整项目。已完成的工作包括分量分划、计算纤维、像值及商值因子化、零化半径和部分覆盖数估计；尚未完成的部分包括七点反例、阶跃函数反例，以及第 3.1、3.3–3.5 题中的若干具体构造与计算。

这些内容源自 Zhe Li（Glen Li）的 *The Operator Evolution Theory*, Volume I，CC BY 4.0，https://glenzli.com/books/oet/ 。

以下给出一个可独立编译的较小部分项目；它不代表上文全部已探索工作的完整交付。其余义务均在清单中明确标为 `incomplete`。

```lean filename=Main.lean
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling

/-!
Partial formalization of Chapter 3 of Zhe Li, The Operator Evolution Theory,
Volume I, v1.0.0, https://glenzli.com/books/oet/, CC BY 4.0.
-/

namespace Chapter3

open Set
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X}

def constComponents (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}

def identityComponents (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) : Set I :=
  {i | i ∉ constComponents d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}

def activeComponents (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) : Set I :=
  (constComponents d f U ∪ identityComponents d f U)ᶜ

theorem components_partition (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) :
    (i ∈ constComponents d f U ∨ i ∈ identityComponents d f U ∨
      i ∈ activeComponents d f U) ∧
    ¬ (i ∈ constComponents d f U ∧ i ∈ identityComponents d f U) ∧
    ¬ (i ∈ constComponents d f U ∧ i ∈ activeComponents d f U) ∧
    ¬ (i ∈ identityComponents d f U ∧ i ∈ activeComponents d f U) := by
  classical
  simp only [identityComponents, activeComponents, mem_setOf_eq, mem_compl_iff,
    mem_union]
  tauto

theorem const_zero_row [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I)
    (hi : i ∈ constComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) ≤
      ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  simp [hi x hx y hy]

theorem const_colip_zero [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i k : I) (K : I → I → ENNReal)
    (hi : i ∈ constComponents d f U) (hK : IsCoLipMatrix d f U K)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (hpos : 0 < d k x y) : K k i = 0 :=
  colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy
    (hi x hx y hy) hpos

theorem dist_eq_of_zero_endpoints (d : X → X → ENNReal)
    (hs : ∀ x y, d x y = d y x)
    (ht : ∀ x y z, d x z ≤ d x y + d y z)
    {a b c e : X} (hab : d a b = 0) (hce : d c e = 0) :
    d a c = d b e := by
  have hba : d b a = 0 := by rw [hs b a, hab]
  have hec : d e c = 0 := by rw [hs e c, hce]
  apply le_antisymm
  · calc
      d a c ≤ d a b + d b c := ht a b c
      _ ≤ d a b + (d b e + d e c) := add_le_add le_rfl (ht b e c)
      _ = d b e := by simp [hab, hec]
  · calc
      d b e ≤ d b a + d a e := ht b a e
      _ ≤ d b a + (d a c + d c e) := add_le_add le_rfl (ht a c e)
      _ = d a c := by simp [hba, hce]

theorem identity_preserves_distance (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hi : i ∈ identityComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = d i x y := by
  intro x hx y hy
  exact dist_eq_of_zero_endpoints (d i) hd.symm hd.triangle (hi.2 x hx) (hi.2 y hy)

theorem outer_const (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (i : I)
    (h : i ∈ constComponents d g (f.func '' U)) :
    i ∈ constComponents d (g * f) U := by
  intro x hx y hy
  exact h (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩

theorem inner_const_of_single_row [Fintype I] (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (j : I) (L : I → I → ENNReal)
    (hc : j ∈ constComponents d f U)
    (hL : IsLipMatrix d g (f.func '' U) L)
    (hrow : ∀ k, k ≠ j → L k j = 0) :
    j ∈ constComponents d (g * f) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hL hrow
      (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
  simpa [hc x hx y hy] using h

theorem identity_comp (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hf : i ∈ identityComponents d f U)
    (hg : i ∈ identityComponents d g (f.func '' U)) :
    i ∈ identityComponents d (g * f) U := by
  constructor
  · intro hc
    apply hf.1
    intro x hx y hy
    have heq := identity_preserves_distance d g (f.func '' U) i hd hg
      (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
    exact heq.symm.trans (hc x hx y hy)
  · intro x hx
    apply le_antisymm _ (zero_le _)
    calc
      d i ((g * f).func x) x ≤
          d i (g.func (f.func x)) (f.func x) + d i (f.func x) x :=
        hd.triangle _ _ _
      _ = 0 := by rw [hg.2 _ ⟨x, hx, rfl⟩, hf.2 x hx, add_zero]

theorem active_comp (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i)) :
    i ∈ activeComponents d (g * f) U →
      i ∈ activeComponents d f U ∨
        i ∈ activeComponents d g (f.func '' U) := by
  classical
  intro hc
  by_contra h
  have hf : i ∈ constComponents d f U ∨ i ∈ identityComponents d f U := by
    have h1 := (not_or.mp h).1
    simp only [activeComponents, mem_compl_iff, mem_union] at h1
    tauto
  have hg : i ∈ constComponents d g (f.func '' U) ∨
      i ∈ identityComponents d g (f.func '' U) := by
    have h2 := (not_or.mp h).2
    simp only [activeComponents, mem_compl_iff, mem_union] at h2
    tauto
  have hnot : i ∉ constComponents d (g * f) U ∧
      i ∉ identityComponents d (g * f) U := by
    simpa [activeComponents] using hc
  rcases hg with hg | hg
  · exact hnot.1 (outer_const d f g U i hg)
  · rcases hf with hf | hf
    · apply hnot.1
      intro x hx y hy
      have heq := identity_preserves_distance d g (f.func '' U) i hd hg
        (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
      exact heq.trans (hf x hx y hy)
    · exact hnot.2 (identity_comp d f g U i hd hf hg)

def seqOp : List (Operator X bot) → Operator X bot
  | [] => 1
  | f :: fs => seqOp fs * f

def seqActive (d : I → X → X → ENNReal) :
    List (Operator X bot) → Set X → Set I
  | [], _ => ∅
  | f :: fs, U => activeComponents d f U ∪ seqActive d fs (f.func '' U)

theorem seqOp_eq_reverse_prod (fs : List (Operator X bot)) :
    seqOp fs = fs.reverse.prod := by
  induction fs with
  | nil => rfl
  | cons f fs ih => simp [seqOp, ih, List.prod_append]

theorem identity_not_active (d : I → X → X → ENNReal)
    (U : Set X) (i : I) (hself : ∀ x, d i x x = 0) :
    i ∉ activeComponents d (1 : Operator X bot) U := by
  classical
  simp only [activeComponents, mem_compl_iff, mem_union, not_not]
  by_cases hc : i ∈ constComponents d (1 : Operator X bot) U
  · exact Or.inl hc
  · right
    exact ⟨hc, fun x _ => hself x⟩

theorem active_seq (d : I → X → X → ENNReal)
    (fs : List (Operator X bot)) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i)) :
    i ∈ activeComponents d (seqOp fs) U → i ∈ seqActive d fs U := by
  induction fs generalizing U with
  | nil =>
      intro h
      exact (identity_not_active d U i hd.dist_self h).elim
  | cons f fs ih =>
      intro h
      rcases active_comp d f (seqOp fs) U i hd h with h | h
      · exact Or.inl h
      · exact Or.inr (ih (f.func '' U) h)

def fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ subfamily_pseudometric d J (f.func x) y = 0}

def componentFiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ d j (f.func x) y = 0}

theorem subfamily_zero_iff (d : I → X → X → ENNReal)
    (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    apply le_antisymm _ (zero_le _)
    calc
      d j x y ≤ subfamily_pseudometric d J x y :=
        le_iSup (fun k : {k // k ∈ J} => d k.1 x y) ⟨j, hj⟩
      _ = 0 := h
  · intro h
    apply le_antisymm _ (zero_le _)
    apply iSup_le
    intro j
    exact le_of_eq (h j.1 j.2)

theorem fiber_components (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) :
    fiber d f J y U =
      {x | x ∈ U ∧ ∀ j ∈ J, x ∈ componentFiber d f j y U} := by
  ext x
  simp only [fiber, componentFiber, mem_setOf_eq, subfamily_zero_iff]
  constructor
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun j hj => ⟨hx, h j hj⟩⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, fun j hj => (h j hj).2⟩

theorem fiber_intersection (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) (hJ : J.Nonempty) :
    fiber d f J y U = ⋂ j ∈ J, componentFiber d f j y U := by
  rw [fiber_components]
  ext x
  simp only [mem_setOf_eq, mem_iInter]
  constructor
  · exact And.right
  · intro h
    obtain ⟨j, hj⟩ := hJ
    exact ⟨(h j hj).1, h⟩

theorem fiber_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    (J K : Set I) (y : X) (U : Set X) (hJK : J ⊆ K) :
    fiber d f K y U ⊆ fiber d f J y U := by
  intro x hx
  exact ⟨hx.1, (subfamily_zero_iff d J _ _).2
    (fun j hj => (subfamily_zero_iff d K _ _).1 hx.2 j (hJK hj))⟩

theorem fiber_singleton (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) :
    fiber d f {j} y U = componentFiber d f j y U := by
  ext x
  simp [fiber, componentFiber, subfamily_pseudometric_singleton]

theorem fiber_all_subset (d : I → X → X → ENNReal) (f : Operator X bot)
    (j : I) (y : X) (U : Set X) :
    fiber d f univ y U ⊆ componentFiber d f j y U := by
  rw [← fiber_singleton]
  exact fiber_antitone d f _ _ _ _ (subset_univ _)

theorem fiber_target_zero (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y z : X) (U : Set X)
    (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    (hyz : subfamily_pseudometric d J y z = 0) :
    fiber d f J y U = fiber d f J z U := by
  ext x
  simp only [fiber, mem_setOf_eq, subfamily_zero_iff]
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩ <;> intro j hj
  · apply le_antisymm _ (zero_le _)
    calc
      d j (f.func x) z ≤ d j (f.func x) y + d j y z := (hd j).triangle _ _ _
      _ = 0 := by
        rw [h.2 j hj, (subfamily_zero_iff d J y z).1 hyz j hj, add_zero]
  · apply le_antisymm _ (zero_le _)
    calc
      d j (f.func x) y ≤ d j (f.func x) z + d j z y := (hd j).triangle _ _ _
      _ = 0 := by
        rw [h.2 j hj, (hd j).symm z y,
          (subfamily_zero_iff d J y z).1 hyz j hj, add_zero]

theorem fiber_image_cover (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (U : Set X) (hd : ∀ j, ExtendedPseudoMetric X bot (d j)) :
    (∀ y ∈ f.func '' U, (fiber d f J y U).Nonempty) ∧
    (⋃ y ∈ f.func '' U, fiber d f J y U) = U := by
  constructor
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨x, hx, (subfamily_zero_iff d J _ _).2
      (fun j _ => (hd j).dist_self _)⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨y, _, hxy⟩ := Set.mem_iUnion₂.mp hx
      exact hxy.1
    · intro hx
      apply Set.mem_iUnion₂.mpr
      exact ⟨f.func x, ⟨x, hx, rfl⟩, hx,
        (subfamily_zero_iff d J _ _).2 (fun j _ => (hd j).dist_self _)⟩

theorem fiber_equal_or_disjoint (d : I → X → X → ENNReal)
    (f : Operator X bot) (J : Set I) (U : Set X) (y z : X)
    (hd : ∀ j, ExtendedPseudoMetric X bot (d j)) :
    fiber d f J y U = fiber d f J z U ∨
      Disjoint (fiber d f J y U) (fiber d f J z U) := by
  classical
  by_cases h : Disjoint (fiber d f J y U) (fiber d f J z U)
  · exact Or.inr h
  · left
    have hex : ∃ x, x ∈ fiber d f J y U ∧ x ∈ fiber d f J z U :=
      Set.not_disjoint_iff.mp h
    obtain ⟨x, hx, hx'⟩ := hex
    apply fiber_target_zero d f J y z U hd
    apply (subfamily_zero_iff d J y z).2
    intro j hj
    apply le_antisymm _ (zero_le _)
    calc
      d j y z ≤ d j y (f.func x) + d j (f.func x) z := (hd j).triangle _ _ _
      _ = 0 := by
        rw [(hd j).symm y (f.func x),
          (subfamily_zero_iff d J _ _).1 hx.2 j hj,
          (subfamily_zero_iff d J _ _).1 hx'.2 j hj, add_zero]

theorem identity_component_fiber (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y : X)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hi : i ∈ identityComponents d f U) :
    componentFiber d f i y U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  simp only [componentFiber, mem_setOf_eq]
  constructor <;> intro h <;> refine ⟨h.1, ?_⟩
  · have hdist := dist_eq_of_zero_endpoints (d i) hd.symm hd.triangle
      (hi.2 x h.1) (hd.dist_self y)
    exact hdist.symm.trans h.2
  · have hdist := dist_eq_of_zero_endpoints (d i) hd.symm hd.triangle
      (hi.2 x h.1) (hd.dist_self y)
    exact hdist.trans h.2

theorem constant_component_fiber (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (y₀ y : X)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hc : i ∈ constComponents d f U) (hy₀ : y₀ ∈ f.func '' U) :
    componentFiber d f i y₀ U = U ∧
      (0 < d i y y₀ → componentFiber d f i y U = ∅) := by
  obtain ⟨z, hz, rfl⟩ := hy₀
  constructor
  · ext x
    simp only [componentFiber, mem_setOf_eq]
    constructor
    · exact And.left
    · intro hx
      exact ⟨hx, hc x hx z hz⟩
  · intro hpos
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have hzero : d i y (f.func z) = 0 := by
      apply le_antisymm _ (zero_le _)
      calc
        d i y (f.func z) ≤ d i y (f.func x) + d i (f.func x) (f.func z) :=
          hd.triangle _ _ _
        _ = 0 := by
          rw [hd.symm y (f.func x), hx.2, hc x hx.1 z hz, add_zero]
    exact (ne_of_gt hpos) hzero

end Chapter3
```

```json filename=alignment.json
{
  "case_id": "MG-C003",
  "version": "0.1.1",
  "items": [
    {"id":"CH03-D01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.constComponents"},{"file":"Main.lean","name":"Chapter3.identityComponents"},{"file":"Main.lean","name":"Chapter3.activeComponents"},{"file":"Main.lean","name":"Chapter3.components_partition"}],"representation":"U 上常值、非恒常逐点零距与剩余分量；证明常值优先的互斥穷尽。","dependencies":[]},
    {"id":"CH03-D02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber"},{"file":"Main.lean","name":"Chapter3.componentFiber"},{"file":"Main.lean","name":"Chapter3.subfamily_zero_iff"},{"file":"Main.lean","name":"Chapter3.fiber_intersection"}],"representation":"以冻结子族复合伪度量的零距离和 U 成员定义纤维，证明与分量条件及交集的对应。","dependencies":[]},
    {"id":"CH03-D03","status":"incomplete","declarations":[],"representation":"点值关系、零距关系、像商和纤维预序尚未在本文件交付。","dependencies":[]},
    {"id":"CH03-D04","status":"incomplete","declarations":[],"representation":"点态零化半径及其球包含对应尚未交付。","dependencies":[]},
    {"id":"CH03-D05","status":"incomplete","declarations":[],"representation":"统一半径与零化矩阵尚未交付。","dependencies":[]},
    {"id":"CH03-D06","status":"incomplete","declarations":[],"representation":"输入尺度与阈值分类尚未交付。","dependencies":[]},
    {"id":"CH03-D07","status":"incomplete","declarations":[],"representation":"尚未交付覆盖数、熵和全有界接口的全部对应证明。","dependencies":[]},
    {"id":"CH03-D08","status":"incomplete","declarations":[],"representation":"映射熵差及其良定域尚未交付。","dependencies":[]},
    {"id":"CH03-P01-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.const_zero_row"}],"representation":"常值输出在任意 x,y∈U 为零，零行有限和也为零。","dependencies":["CH03-D01"]},
    {"id":"CH03-P01-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.const_colip_zero"}],"representation":"输出零距和正输入距离迫使合法 co-Lip 条目为零。","dependencies":["CH03-D01"]},
    {"id":"CH03-P01-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.identity_preserves_distance"},{"file":"Main.lean","name":"Chapter3.dist_eq_of_zero_endpoints"}],"representation":"每个端点与其像零距，三角不等式双向给出距离相等。","dependencies":["CH03-D01"]},
    {"id":"CH03-P02-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.active_comp"}],"representation":"g*f 表示先 f 后 g；第二步限制域是实际像 f(U)。","dependencies":["CH03-D01","CH03-P01-03","CH03-P02-03","CH03-P04-01"]},
    {"id":"CH03-P02-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.seqOp"},{"file":"Main.lean","name":"Chapter3.seqActive"},{"file":"Main.lean","name":"Chapter3.seqOp_eq_reverse_prod"},{"file":"Main.lean","name":"Chapter3.active_seq"}],"representation":"列表按输入先后递归，每步使用实际像域；证明任意长度及空链。","dependencies":["CH03-D01","CH03-P02-01"]},
    {"id":"CH03-P02-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.identity_comp"}],"representation":"逐点零距传递且保距排除复合落入常值优先分支。","dependencies":["CH03-D01","CH03-P01-03"]},
    {"id":"CH03-P03-01","status":"incomplete","declarations":[],"representation":"两点换位反例的合法结构和完整计算尚未交付。","dependencies":[]},
    {"id":"CH03-P04-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.outer_const"}],"representation":"外侧在内侧实际像域上常值，故复合在 U 上常值。","dependencies":["CH03-D01"]},
    {"id":"CH03-P04-02","status":"incomplete","declarations":[],"representation":"七点双分量反例尚未交付。","dependencies":[]},
    {"id":"CH03-P05-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.inner_const_of_single_row"}],"representation":"实际像域上的指定单行 Lip 界传递内侧常值，系数可为无穷。","dependencies":["CH03-D01"]},
    {"id":"CH03-P06-01","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_target_zero"}],"representation":"任意目标子族零距时纤维相等。","dependencies":["CH03-D02"]},
    {"id":"CH03-P06-02","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_image_cover"}],"representation":"每个像目标纤维非空，所有像目标纤维覆盖 U。","dependencies":["CH03-D02"]},
    {"id":"CH03-P06-03","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_equal_or_disjoint"},{"file":"Main.lean","name":"Chapter3.fiber_image_cover"}],"representation":"纤维相等或不交，并结合非空性与覆盖得到去重分划。","dependencies":["CH03-D02","CH03-P06-01","CH03-P06-02"]},
    {"id":"CH03-P06-04","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_intersection"}],"representation":"非空子族纤维等于其单分量纤维的交集。","dependencies":["CH03-D02"]},
    {"id":"CH03-P06-05","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_antitone"}],"representation":"J⊆K 时 K 纤维包含于 J 纤维。","dependencies":["CH03-D02"]},
    {"id":"CH03-P06-06","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.fiber_singleton"},{"file":"Main.lean","name":"Chapter3.fiber_all_subset"}],"representation":"单元素子族恢复该分量，全指标纤维包含每个单分量纤维。","dependencies":["CH03-D02","CH03-P06-05"]},
    {"id":"CH03-P06-07","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.identity_component_fiber"}],"representation":"恒等分量下任意目标的输出纤维等于 U 内输入零距类。","dependencies":["CH03-D01","CH03-D02"]},
    {"id":"CH03-P06-08","status":"complete","declarations":[{"file":"Main.lean","name":"Chapter3.constant_component_fiber"}],"representation":"常值分量的像目标纤维为 U，正距离目标纤维为空。","dependencies":["CH03-D01","CH03-D02"]},
    {"id":"CH03-P07-01","status":"incomplete","declarations":[],"representation":"点值因子化必要性尚未交付。","dependencies":[]},
    {"id":"CH03-P07-02","status":"incomplete","declarations":[],"representation":"像点代表元构造及空域分支尚未交付。","dependencies":[]},
    {"id":"CH03-P07-03","status":"incomplete","declarations":[],"representation":"双向点值变换判据尚未交付。","dependencies":[]},
    {"id":"CH03-P07-04","status":"incomplete","declarations":[],"representation":"实际像域上的 LB/KA 界尚未交付。","dependencies":[]},
    {"id":"CH03-P08-01","status":"incomplete","declarations":[],"representation":"单向零距商映射构造及判据尚未交付。","dependencies":[]},
    {"id":"CH03-P08-02","status":"incomplete","declarations":[],"representation":"双向商映射判据尚未交付。","dependencies":[]},
    {"id":"CH03-P08-03","status":"incomplete","declarations":[],"representation":"实际像集分离时的两类判据对应尚未交付。","dependencies":[]},
    {"id":"CH03-P09-01","status":"incomplete","declarations":[],"representation":"纤维预序自反性与传递性尚未交付。","dependencies":[]},
    {"id":"CH03-P09-02","status":"incomplete","declarations":[],"representation":"有限链任意两层的包含尚未交付。","dependencies":[]},
    {"id":"CH03-P09-03","status":"incomplete","declarations":[],"representation":"链中真包含到端点真包含的差集见证尚未交付。","dependencies":[]},
    {"id":"CH03-P10-01","status":"incomplete","declarations":[],"representation":"实线阶跃反例的合法结构尚未交付。","dependencies":[]},
    {"id":"CH03-P10-02","status":"incomplete","declarations":[],"representation":"阶跃反例的点态合法半径计算尚未交付。","dependencies":[]},
    {"id":"CH03-P10-03","status":"incomplete","declarations":[],"representation":"阶跃反例统一半径为零的证明尚未交付。","dependencies":[]},
    {"id":"CH03-P11-01","status":"incomplete","declarations":[],"representation":"常值子族的像目标纤维结论尚未完整交付。","dependencies":[]},
    {"id":"CH03-P11-02","status":"incomplete","declarations":[],"representation":"常值子族的点态及统一半径为无穷尚未交付。","dependencies":[]},
    {"id":"CH03-P11-03","status":"incomplete","declarations":[],"representation":"两种通道情形的无穷输入距离反例尚未交付。","dependencies":[]},
    {"id":"CH03-P12-01","status":"incomplete","declarations":[],"representation":"恒等分量的像目标纤维公式尚未交付。","dependencies":[]},
    {"id":"CH03-P12-02","status":"incomplete","declarations":[],"representation":"恒等分量的点态半径下界尚未交付。","dependencies":[]},
    {"id":"CH03-P13-01","status":"incomplete","declarations":[],"representation":"有限子族点态半径最小值公式尚未交付。","dependencies":[]},
    {"id":"CH03-P13-02","status":"incomplete","declarations":[],"representation":"统一半径最小值公式及下确界交换尚未交付。","dependencies":[]},
    {"id":"CH03-P13-03","status":"incomplete","declarations":[],"representation":"统一半径关于输出子族的反单调性尚未交付。","dependencies":[]},
    {"id":"CH03-P14-01","status":"incomplete","declarations":[],"representation":"纤维成员推出输出零距的专门声明尚未交付。","dependencies":[]},
    {"id":"CH03-P14-02","status":"incomplete","declarations":[],"representation":"从点态半径严格上确界提取合法半径尚未交付。","dependencies":[]},
    {"id":"CH03-P14-03","status":"incomplete","declarations":[],"representation":"纤维判据的复合输入实例尚未交付。","dependencies":[]},
    {"id":"CH03-P15-01","status":"incomplete","declarations":[],"representation":"零距保持下的复合统一半径下界尚未交付。","dependencies":[]},
    {"id":"CH03-P15-02","status":"incomplete","declarations":[],"representation":"Lip 拉回的复合统一半径下界及边界尚未交付。","dependencies":[]},
    {"id":"CH03-P16-01","status":"incomplete","declarations":[],"representation":"四种阈值组合的互斥穷尽尚未交付。","dependencies":[]},
    {"id":"CH03-P16-02","status":"incomplete","declarations":[],"representation":"输入尺度阈值增大时的单调性尚未交付。","dependencies":[]},
    {"id":"CH03-P16-03","status":"incomplete","declarations":[],"representation":"零化阈值增大时的反单调性尚未交付。","dependencies":[]},
    {"id":"CH03-P17-01","status":"incomplete","declarations":[],"representation":"域缩小时尺度及阈值单调性尚未交付。","dependencies":[]},
    {"id":"CH03-P17-02","status":"incomplete","declarations":[],"representation":"缩小评估域时的点态半径单调性尚未交付。","dependencies":[]},
    {"id":"CH03-P17-03","status":"incomplete","declarations":[],"representation":"缩小域时的统一半径单调性尚未交付。","dependencies":[]},
    {"id":"CH03-P17-04","status":"incomplete","declarations":[],"representation":"直径尺度的二点单点反例尚未交付。","dependencies":[]},
    {"id":"CH03-P18-01","status":"incomplete","declarations":[],"representation":"低于统一半径的零化判据尚未交付。","dependencies":[]},
    {"id":"CH03-P18-02","status":"incomplete","declarations":[],"representation":"输出正分离时的输入距离下界尚未交付。","dependencies":[]},
    {"id":"CH03-P18-03","status":"incomplete","declarations":[],"representation":"对每个规定 α 的有限正分离见证尚未交付。","dependencies":[]},
    {"id":"CH03-P19-01","status":"incomplete","declarations":[],"representation":"阈值球到纤维的包含尚未交付。","dependencies":[]},
    {"id":"CH03-P19-02","status":"incomplete","declarations":[],"representation":"含空集及无有限覆盖情形的覆盖数约束尚未交付。","dependencies":[]},
    {"id":"CH03-P19-03","status":"incomplete","declarations":[],"representation":"覆盖数约束对应的熵不等式尚未交付。","dependencies":[]},
    {"id":"CH03-P20-01","status":"incomplete","declarations":[],"representation":"阶跃反例上任意输入尺度的二点覆盖构造尚未交付。","dependencies":[]},
    {"id":"CH03-P21-01","status":"incomplete","declarations":[],"representation":"小直径条件下整体零化的双向判据尚未交付。","dependencies":[]},
    {"id":"CH03-P21-02","status":"incomplete","declarations":[],"representation":"整体零化时输出覆盖数为一尚未交付。","dependencies":[]},
    {"id":"CH03-P22-01","status":"incomplete","declarations":[],"representation":"有限非空集上的覆盖、有限熵和熵差良定性尚未交付。","dependencies":[]},
    {"id":"CH03-P23-01","status":"incomplete","declarations":[],"representation":"常值分量输出覆盖数、熵和熵差尚未交付。","dependencies":[]},
    {"id":"CH03-P23-02","status":"incomplete","declarations":[],"representation":"恒等分量的双向内部覆盖数比较尚未交付。","dependencies":[]},
    {"id":"CH03-P23-03","status":"incomplete","declarations":[],"representation":"恒等分量在良定条件下熵差为零尚未交付。","dependencies":[]},
    {"id":"CH03-P24-01","status":"incomplete","declarations":[],"representation":"单通道 Lip 输入覆盖推到输出覆盖尚未交付。","dependencies":[]},
    {"id":"CH03-P24-02","status":"incomplete","declarations":[],"representation":"全有界条件下的熵差下界尚未交付。","dependencies":[]},
    {"id":"CH03-P25-01","status":"incomplete","declarations":[],"representation":"正有限 co-Lip 条目的覆盖数下界尚未交付。","dependencies":[]},
    {"id":"CH03-P25-02","status":"incomplete","declarations":[],"representation":"允许输出熵无穷的熵差上界尚未交付。","dependencies":[]},
    {"id":"CH03-P26-01","status":"incomplete","declarations":[],"representation":"习题 3.1 的结构合法性、一次纤维与类型尚未交付。","dependencies":[]},
    {"id":"CH03-P26-02","status":"incomplete","declarations":[],"representation":"习题 3.1 的自复合纤维与类型尚未交付。","dependencies":[]},
    {"id":"CH03-P26-03","status":"incomplete","declarations":[],"representation":"点值常算子的自复合及吸收元分支尚未交付。","dependencies":[]},
    {"id":"CH03-P27-01","status":"incomplete","declarations":[],"representation":"正 co-Lip 与点态半径给出的距离间隙尚未交付。","dependencies":[]},
    {"id":"CH03-P27-02","status":"incomplete","declarations":[],"representation":"统一半径给出的距离二择尚未交付。","dependencies":[]},
    {"id":"CH03-P28-01","status":"incomplete","declarations":[],"representation":"习题 3.3 的两种纤维分划及结构尚未交付。","dependencies":[]},
    {"id":"CH03-P28-02","status":"incomplete","declarations":[],"representation":"习题 3.3 的覆盖数上下界和熵差尚未交付。","dependencies":[]},
    {"id":"CH03-P29-01","status":"incomplete","declarations":[],"representation":"习题 3.4 第一个域的直径、半径和类型尚未交付。","dependencies":[]},
    {"id":"CH03-P29-02","status":"incomplete","declarations":[],"representation":"习题 3.4 第二个域的直径、半径和类型尚未交付。","dependencies":[]},
    {"id":"CH03-P29-03","status":"incomplete","declarations":[],"representation":"习题 3.4 第三个域的直径、半径和类型尚未交付。","dependencies":[]},
    {"id":"CH03-P29-04","status":"incomplete","declarations":[],"representation":"习题 3.4 第四个域的直径、半径和类型尚未交付。","dependencies":[]},
    {"id":"CH03-P29-05","status":"incomplete","declarations":[],"representation":"习题 3.4 无直径条件时的合法反例尚未交付。","dependencies":[]},
    {"id":"CH03-P30-01","status":"incomplete","declarations":[],"representation":"四点集全部精度与端点的内部覆盖数尚未交付。","dependencies":[]},
    {"id":"CH03-P30-02","status":"incomplete","declarations":[],"representation":"两个像集及全部精度的覆盖数和熵差尚未交付。","dependencies":[]},
    {"id":"CH03-P30-03","status":"incomplete","declarations":[],"representation":"两个最优标量 Lip 常数及必要下界尚未交付。","dependencies":[]},
    {"id":"CH03-P30-04","status":"incomplete","declarations":[],"representation":"精度 7/4 时一般覆盖界和真实值的比较尚未交付。","dependencies":[]}
  ]
}
```