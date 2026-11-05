import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Set.Basic
import OperatorLocalDegeneracy.ComponentPartition

namespace OperatorLocalDegeneracy

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
set_option linter.deprecated false

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

/-- CH03-D02: 计算纤维 -/
def Fib (ϕ : Operator X bot) (J : Set I) (y : X) (U : Set X) : Set X :=
  { x ∈ U | subfamily_pseudometric d J (ϕ.func x) y = 0 }

def Fib_single (ϕ : Operator X bot) (j : I) (y : X) (U : Set X) : Set X :=
  { x ∈ U | d j (ϕ.func x) y = 0 }

/-- CH03-D03: 点值关系 -/
def R_eq (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  { p : X × X | p.1 ∈ U ∧ p.2 ∈ U ∧ ϕ.func p.1 = ϕ.func p.2 }

/-- CH03-D03: 零距关系 -/
def R_zero (ϕ : Operator X bot) (U : Set X) : Set (X × X) :=
  { p : X × X | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (ϕ.func p.1) (ϕ.func p.2) }

/-- CH03-D03: 零测距纤维预序 -/
def fiber_preorder (U : Set X) (ϕA ϕB : Operator X bot) : Prop :=
  R_zero d ϕA U ⊆ R_zero d ϕB U

/-- CH03-P06-01: 命题 3.5 (i) 任意目标零距时纤维相等 -/
theorem prop_3_5_i (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (J : Set I) (hJ : J.Nonempty) (y y' : X) (U : Set X)
    (hy : subfamily_pseudometric d J y y' = 0) :
    Fib d ϕ J y U = Fib d ϕ J y' U := by
  have hdJ := subfamily_pseudometric_is_extended d J hJ hd
  ext x
  simp only [Fib, Set.mem_setOf_eq, and_congr_right_iff]
  intro hx
  constructor
  · intro h
    apply le_antisymm _ (zero_le _)
    calc
      subfamily_pseudometric d J (ϕ.func x) y'
          ≤ subfamily_pseudometric d J (ϕ.func x) y + subfamily_pseudometric d J y y' := hdJ.triangle _ _ _
      _ = 0 + 0 := by rw [h, hy]
      _ = 0 := by simp
  · intro h
    apply le_antisymm _ (zero_le _)
    calc
      subfamily_pseudometric d J (ϕ.func x) y
          ≤ subfamily_pseudometric d J (ϕ.func x) y' + subfamily_pseudometric d J y' y := hdJ.triangle _ _ _
      _ = 0 + 0 := by
        rw [h]
        congr 1
        rw [hdJ.symm, hy]
      _ = 0 := by simp

/-- CH03-P06-02: 命题 3.5 (ii-a) 像目标纤维非空且覆盖U -/
theorem prop_3_5_ii_a (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (J : Set I) (hJ : J.Nonempty) (U : Set X) :
    (∀ y ∈ ϕ.func '' U, (Fib d ϕ J y U).Nonempty) ∧
    (⋃ y ∈ ϕ.func '' U, Fib d ϕ J y U) = U := by
  have hdJ := subfamily_pseudometric_is_extended d J hJ hd
  constructor
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨x, ?_⟩
    simp [Fib, hx, hdJ.dist_self]
  · ext x
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop, Fib, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨x0, hx0, rfl⟩, hx, -⟩
      exact hx
    · intro hx
      refine ⟨ϕ.func x, ⟨x, hx, rfl⟩, hx, hdJ.dist_self _⟩

/-- CH03-P06-03: 命题 3.5 (ii-b) 像目标纤维相等或不交 -/
theorem prop_3_5_ii_b (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (J : Set I) (hJ : J.Nonempty) (U : Set X)
    (y₁ y₂ : X) (hy₁ : y₁ ∈ ϕ.func '' U) (hy₂ : y₂ ∈ ϕ.func '' U) :
    Fib d ϕ J y₁ U = Fib d ϕ J y₂ U ∨ Disjoint (Fib d ϕ J y₁ U) (Fib d ϕ J y₂ U) := by
  have hdJ := subfamily_pseudometric_is_extended d J hJ hd
  by_cases hdisj : Disjoint (Fib d ϕ J y₁ U) (Fib d ϕ J y₂ U)
  · exact Or.inr hdisj
  · left
    rcases Set.not_disjoint_iff.mp hdisj with ⟨x, hx1, hx2⟩
    have hd1 : subfamily_pseudometric d J (ϕ.func x) y₁ = 0 := hx1.2
    have hd2 : subfamily_pseudometric d J (ϕ.func x) y₂ = 0 := hx2.2
    have hy12 : subfamily_pseudometric d J y₁ y₂ = 0 := by
      apply le_antisymm _ (zero_le _)
      calc
        subfamily_pseudometric d J y₁ y₂
            ≤ subfamily_pseudometric d J y₁ (ϕ.func x) + subfamily_pseudometric d J (ϕ.func x) y₂ := hdJ.triangle _ _ _
        _ = 0 + 0 := by rw [hdJ.symm, hd1, hd2]
        _ = 0 := by simp
    exact prop_3_5_i d hd ϕ J hJ y₁ y₂ U hy12

/-- CH03-P06-04: 命题 3.5 (iii) 有限非空子族的分量交集等式 -/
theorem prop_3_5_iii
    (ϕ : Operator X bot) (J : Set I) (hJ : J.Nonempty) (y : X) (U : Set X) :
    Fib d ϕ J y U = ⋂ j ∈ J, Fib_single d ϕ j y U := by
  ext x
  simp only [Fib, Fib_single, subfamily_pseudometric, Set.mem_setOf_eq, Set.mem_iInter]
  constructor
  · intro ⟨hx, hsup⟩ j hj
    refine ⟨hx, ?_⟩
    have hj_le : d j (ϕ.func x) y ≤ ⨆ k : {k // k ∈ J}, d k.1 (ϕ.func x) y :=
      le_iSup (fun k : {k // k ∈ J} => d k.1 (ϕ.func x) y) ⟨j, hj⟩
    rw [hsup] at hj_le
    exact le_antisymm hj_le (zero_le _)
  · intro h
    obtain ⟨j0, hj0⟩ := hJ
    have hxU : x ∈ U := (h j0 hj0).1
    refine ⟨hxU, ?_⟩
    apply le_antisymm _ (zero_le _)
    apply iSup_le
    rintro ⟨j, hj⟩
    exact (h j hj).2.le

/-- CH03-P06-05: 命题 3.5 (iv) 子族扩大时纤维缩小 -/
theorem prop_3_5_iv
    (ϕ : Operator X bot) (J K : Set I) (hJK : J ⊆ K) (y : X) (U : Set X) :
    Fib d ϕ K y U ⊆ Fib d ϕ J y U := by
  intro x hx
  simp only [Fib, Set.mem_setOf_eq] at hx ⊢
  refine ⟨hx.1, ?_⟩
  apply le_antisymm _ (zero_le _)
  dsimp [subfamily_pseudometric]
  apply iSup_le
  rintro ⟨j, hj⟩
  have hjK : j ∈ K := hJK hj
  have hK_le : d j (ϕ.func x) y ≤ subfamily_pseudometric d K (ϕ.func x) y :=
    le_iSup (fun k : {k // k ∈ K} => d k.1 (ϕ.func x) y) ⟨j, hjK⟩
  rw [hx.2] at hK_le
  exact hK_le

/-- CH03-P06-06: 命题 3.5 (v) 单分量等式及全子族向每分量包含 -/
theorem prop_3_5_v
    (ϕ : Operator X bot) (i : I) (y : X) (U : Set X) :
    Fib d ϕ {i} y U = Fib_single d ϕ i y U ∧
    Fib d ϕ (Set.univ : Set I) y U ⊆ Fib_single d ϕ i y U := by
  constructor
  · ext x
    simp [Fib, Fib_single, subfamily_pseudometric_singleton]
  · intro x hx
    have hsub : Fib d ϕ (Set.univ : Set I) y U ⊆ Fib d ϕ {i} y U :=
      prop_3_5_iv d ϕ {i} Set.univ (Set.subset_univ _) y U
    have h1 := hsub hx
    rw [show Fib d ϕ {i} y U = Fib_single d ϕ i y U from by ext z; simp [Fib, Fib_single, subfamily_pseudometric_singleton]] at h1
    exact h1

/-- CH03-P06-07: 命题 3.5 (vi-a) 恒等分量的任意目标纤维等于输入零距类 -/
theorem prop_3_5_vi_a (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (j : I) (hj : j ∈ I_id d ϕ U) (y : X) :
    Fib_single d ϕ j y U = { x ∈ U | d j x y = 0 } := by
  ext x
  simp only [Fib_single, Set.mem_setOf_eq, and_congr_right_iff]
  intro hx
  have hphi : d j (ϕ.func x) x = 0 := hj.2 x hx
  constructor
  · intro h
    apply le_antisymm _ (zero_le _)
    calc
      d j x y ≤ d j x (ϕ.func x) + d j (ϕ.func x) y := (hd j).triangle _ _ _
      _ = 0 + 0 := by rw [(hd j).symm, hphi, h]
      _ = 0 := by simp
  · intro h
    apply le_antisymm _ (zero_le _)
    calc
      d j (ϕ.func x) y ≤ d j (ϕ.func x) x + d j x y := (hd j).triangle _ _ _
      _ = 0 + 0 := by rw [hphi, h]
      _ = 0 := by simp

/-- CH03-P06-08: 命题 3.5 (vi-b) 常值分量在像目标的纤维为U，正距离目标的纤维为空 -/
theorem prop_3_5_vi_b (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (j : I) (hj : j ∈ I_const d ϕ U) (y y₀ : X)
    (hy₀ : y₀ ∈ ϕ.func '' U) :
    (Fib_single d ϕ j y₀ U = U) ∧
    (0 < d j y y₀ → Fib_single d ϕ j y U = ∅) := by
  rcases hy₀ with ⟨x0, hx0, rfl⟩
  constructor
  · ext x
    simp only [Fib_single, Set.mem_setOf_eq]
    constructor
    · exact fun h => h.1
    · intro hx
      exact ⟨hx, hj x hx x0 hx0⟩
  · intro hpos
    ext x
    simp only [Fib_single, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hx, hzero⟩
    have hconst := hj x hx x0 hx0
    have htri : d j y (ϕ.func x0) ≤ d j y (ϕ.func x) + d j (ϕ.func x) (ϕ.func x0) :=
      (hd j).triangle _ _ _
    have hzero' : d j y (ϕ.func x) = 0 := by rw [(hd j).symm]; exact hzero
    rw [hzero', hconst, add_zero] at htri
    exact (not_lt_of_ge htri) hpos

/-- CH03-P07-01: 命题 3.6 (i-必要) 点值像映射存在推出相等关系包含 -/
theorem prop_3_6_i_nec (ϕA ϕB : Operator X bot) (U : Set X)
    (hT : ∃ T : X → X, ∀ x ∈ U, T (ϕA.func x) = ϕB.func x) :
    R_eq ϕA U ⊆ R_eq ϕB U := by
  rcases hT with ⟨T, hT⟩
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  calc
    ϕB.func x = T (ϕA.func x) := (hT x hx).symm
    _ = T (ϕA.func y) := by rw [hxy]
    _ = ϕB.func y := hT y hy

/-- CH03-P07-02: 命题 3.6 (i-充分) 从关系包含实际构造良定义映射并验证T∘φA=φB，包括U空集 -/
theorem prop_3_6_i_suff (ϕA ϕB : Operator X bot) (U : Set X)
    (hsub : R_eq ϕA U ⊆ R_eq ϕB U) :
    ∃ T : X → X, ∀ x ∈ U, T (ϕA.func x) = ϕB.func x := by
  classical
  let T : X → X := fun y =>
    if h : ∃ x ∈ U, ϕA.func x = y then
      ϕB.func (Classical.choose h)
    else
      bot
  refine ⟨T, ?_⟩
  intro x hx
  dsimp [T]
  have hex : ∃ x' ∈ U, ϕA.func x' = ϕA.func x := ⟨x, hx, rfl⟩
  rw [dif_pos hex]
  have hspec := Classical.choose_spec hex
  have hreq : (Classical.choose hex, x) ∈ R_eq ϕA U := ⟨hspec.1, hx, hspec.2⟩
  have hreqB := hsub hreq
  exact hreqB.2.2

/-- CH03-P07-03: 命题 3.6 (ii) 双向点值变换存在当且仅当关系相等 -/
theorem prop_3_6_ii (ϕA ϕB : Operator X bot) (U : Set X) :
    ((∃ T : X → X, ∀ x ∈ U, T (ϕA.func x) = ϕB.func x) ∧
     (∃ S : X → X, ∀ x ∈ U, S (ϕB.func x) = ϕA.func x)) ↔
    R_eq ϕA U = R_eq ϕB U := by
  constructor
  · rintro ⟨hT, hS⟩
    exact Set.Subset.antisymm (prop_3_6_i_nec ϕA ϕB U hT) (prop_3_6_i_nec ϕB ϕA U hS)
  · intro heq
    refine ⟨prop_3_6_i_suff ϕA ϕB U heq.subset, prop_3_6_i_suff ϕB ϕA U heq.symm.subset⟩

/-- CH03-P07-04: 命题 3.6 (iii) 实际像域上的LB/KA标量界 -/
theorem prop_3_6_iii {d : X → X → ENNReal}
    (ϕA ϕB : Operator X bot) (U : Set X) (T : X → X)
    (hT : ∀ x ∈ U, T (ϕA.func x) = ϕB.func x)
    (KA LB : ENNReal) (hKA_pos : 0 < KA) (hKA_top : KA ≠ ⊤)
    (hcoLip : ∀ x ∈ U, ∀ y ∈ U, KA * d x y ≤ d (ϕA.func x) (ϕA.func y))
    (hLip : ∀ x ∈ U, ∀ y ∈ U, d (ϕB.func x) (ϕB.func y) ≤ LB * d x y) :
    ∀ y₁ ∈ ϕA.func '' U, ∀ y₂ ∈ ϕA.func '' U,
      d (T y₁) (T y₂) ≤ (LB / KA) * d y₁ y₂ := by
  rintro y₁ ⟨x₁, hx₁, rfl⟩ y₂ ⟨x₂, hx₂, rfl⟩
  rw [hT x₁ hx₁, hT x₂ hx₂]
  have hLip_val := hLip x₁ hx₁ x₂ hx₂
  have hcoLip_val := hcoLip x₁ hx₁ x₂ hx₂
  have h_le : d x₁ x₂ ≤ (d (ϕA.func x₁) (ϕA.func x₂)) * KA⁻¹ := by
    have h1 : KA⁻¹ * (KA * d x₁ x₂) ≤ KA⁻¹ * d (ϕA.func x₁) (ϕA.func x₂) :=
      mul_le_mul_left' hcoLip_val KA⁻¹
    rw [← mul_assoc, ENNReal.inv_mul_cancel (ne_of_gt hKA_pos) hKA_top, one_mul] at h1
    rwa [mul_comm] at h1
  calc
    d (ϕB.func x₁) (ϕB.func x₂) ≤ LB * d x₁ x₂ := hLip_val
    _ ≤ LB * (d (ϕA.func x₁) (ϕA.func x₂) * KA⁻¹) := mul_le_mul_left' h_le LB
    _ = (LB / KA) * d (ϕA.func x₁) (ϕA.func x₂) := by
      change LB * (d (ϕA.func x₁) (ϕA.func x₂) * KA⁻¹) = (LB * KA⁻¹) * d (ϕA.func x₁) (ϕA.func x₂)
      ring

def zero_setoid (S : Set X)
    (hd_refl : ∀ i x, d i x x = 0)
    (hd_symm : ∀ i x y, d i x y = d i y x)
    (hd_tri : ∀ i x y z, d i x z ≤ d i x y + d i y z) : Setoid S where
  r x y := GaugeZeroRelated d x.1 y.1
  iseqv := by
    have hequiv := gauge_zero_related_equivalence d hd_refl hd_symm hd_tri
    exact ⟨fun a => hequiv.refl a.1, fun h => hequiv.symm h, fun h1 h2 => hequiv.trans h1 h2⟩

def ZeroQuot (S : Set X)
    (hd_refl : ∀ i x, d i x x = 0)
    (hd_symm : ∀ i x y, d i x y = d i y x)
    (hd_tri : ∀ i x y z, d i x z ≤ d i x y + d i y z) : Type :=
  Quotient (zero_setoid d S hd_refl hd_symm hd_tri)

def quot_mk (S : Set X)
    (hd_refl : ∀ i x, d i x x = 0)
    (hd_symm : ∀ i x y, d i x y = d i y x)
    (hd_tri : ∀ i x y z, d i x z ≤ d i x y + d i y z)
    (x : S) : ZeroQuot d S hd_refl hd_symm hd_tri :=
  ⟦x⟧

/-- CH03-P08-01: 命题 3.7 (1) 单向商映射存在当且仅当零距关系包含 -/
theorem prop_3_7_one_way
    (hd_refl : ∀ i x, d i x x = 0)
    (hd_symm : ∀ i x y, d i x y = d i y x)
    (hd_tri : ∀ i x y z, d i x z ≤ d i x y + d i y z)
    (ϕA ϕB : Operator X bot) (U : Set X) :
    (∃ (Tbar : ZeroQuot d (ϕA.func '' U) hd_refl hd_symm hd_tri →
               ZeroQuot d (ϕB.func '' U) hd_refl hd_symm hd_tri),
      ∀ (x : X) (hx : x ∈ U),
        Tbar (quot_mk d (ϕA.func '' U) hd_refl hd_symm hd_tri ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩) =
             quot_mk d (ϕB.func '' U) hd_refl hd_symm hd_tri ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩) ↔
    R_zero d ϕA U ⊆ R_zero d ϕB U := by
  let setoidA := zero_setoid d (ϕA.func '' U) hd_refl hd_symm hd_tri
  let setoidB := zero_setoid d (ϕB.func '' U) hd_refl hd_symm hd_tri
  constructor
  · rintro ⟨Tbar, hTbar⟩ ⟨x, y⟩ ⟨hx, hy, hrel⟩
    refine ⟨hx, hy, ?_⟩
    have heq : (⟦⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩⟧ : Quotient setoidA) =
               (⟦⟨ϕA.func y, Set.mem_image_of_mem _ hy⟩⟧ : Quotient setoidA) := by
      apply Quotient.sound
      exact hrel
    have hTeq := congrArg Tbar heq
    have hTx := hTbar x hx
    have hTy := hTbar y hy
    dsimp [quot_mk] at hTx hTy
    rw [hTx, hTy] at hTeq
    exact Quotient.exact hTeq
  · intro hsub
    classical
    let f : (ϕA.func '' U) → Quotient setoidB := fun y =>
      let x := Classical.choose y.2
      ⟦⟨ϕB.func x, Set.mem_image_of_mem _ (Classical.choose_spec y.2).1⟩⟧
    have hresp : ∀ (a b : (ϕA.func '' U)), a ≈ b → f a = f b := by
      intro a b hab
      dsimp [f]
      have ha_spec := Classical.choose_spec a.2
      have hb_spec := Classical.choose_spec b.2
      have hrelA : GaugeZeroRelated d (ϕA.func (Classical.choose a.2)) (ϕA.func (Classical.choose b.2)) := by
        intro i
        rw [ha_spec.2, hb_spec.2]
        exact hab i
      have hreq : (Classical.choose a.2, Classical.choose b.2) ∈ R_zero d ϕA U :=
        ⟨ha_spec.1, hb_spec.1, hrelA⟩
      have hreqB := hsub hreq
      apply Quotient.sound
      exact hreqB.2.2
    refine ⟨Quotient.lift f hresp, ?_⟩
    intro x hx
    dsimp [f, quot_mk]
    have hx_spec := Classical.choose_spec (Set.mem_image_of_mem ϕA.func hx)
    have hrelA : GaugeZeroRelated d (ϕA.func (Classical.choose (Set.mem_image_of_mem ϕA.func hx))) (ϕA.func x) := by
      intro i
      rw [hx_spec.2]
      exact hd_refl i _
    have hreq : (Classical.choose (Set.mem_image_of_mem ϕA.func hx), x) ∈ R_zero d ϕA U :=
      ⟨hx_spec.1, hx, hrelA⟩
    have hreqB := hsub hreq
    apply Quotient.sound
    exact hreqB.2.2

/-- CH03-P08-02: 命题 3.7 (2) 双向商映射存在当且仅当零距关系相等 -/
theorem prop_3_7_two_way
    (hd_refl : ∀ i x, d i x x = 0)
    (hd_symm : ∀ i x y, d i x y = d i y x)
    (hd_tri : ∀ i x y z, d i x z ≤ d i x y + d i y z)
    (ϕA ϕB : Operator X bot) (U : Set X) :
    ((∃ (Tbar : ZeroQuot d (ϕA.func '' U) hd_refl hd_symm hd_tri →
                 ZeroQuot d (ϕB.func '' U) hd_refl hd_symm hd_tri),
        ∀ (x : X) (hx : x ∈ U),
          Tbar (quot_mk d (ϕA.func '' U) hd_refl hd_symm hd_tri ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩) =
               quot_mk d (ϕB.func '' U) hd_refl hd_symm hd_tri ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩) ∧
     (∃ (Sbar : ZeroQuot d (ϕB.func '' U) hd_refl hd_symm hd_tri →
                 ZeroQuot d (ϕA.func '' U) hd_refl hd_symm hd_tri),
        ∀ (x : X) (hx : x ∈ U),
          Sbar (quot_mk d (ϕB.func '' U) hd_refl hd_symm hd_tri ⟨ϕB.func x, Set.mem_image_of_mem _ hx⟩) =
               quot_mk d (ϕA.func '' U) hd_refl hd_symm hd_tri ⟨ϕA.func x, Set.mem_image_of_mem _ hx⟩)) ↔
    R_zero d ϕA U = R_zero d ϕB U := by
  constructor
  · rintro ⟨hT, hS⟩
    have h1 := (prop_3_7_one_way d hd_refl hd_symm hd_tri ϕA ϕB U).mp hT
    have h2 := (prop_3_7_one_way d hd_refl hd_symm hd_tri ϕB ϕA U).mp hS
    exact Set.Subset.antisymm h1 h2
  · intro heq
    refine ⟨(prop_3_7_one_way d hd_refl hd_symm hd_tri ϕA ϕB U).mpr heq.subset,
            (prop_3_7_one_way d hd_refl hd_symm hd_tri ϕB ϕA U).mpr heq.symm.subset⟩

/-- CH03-P08-03: 命题 3.7 (3) 仅在两个实际像集各自分离的条件下，将商判据转回点值判据 -/
theorem prop_3_7_separating
    (hd_refl : ∀ i x, d i x x = 0)
    (ϕA ϕB : Operator X bot) (U : Set X)
    (hsepA : ∀ x ∈ ϕA.func '' U, ∀ y ∈ ϕA.func '' U, GaugeZeroRelated d x y → x = y)
    (hsepB : ∀ x ∈ ϕB.func '' U, ∀ y ∈ ϕB.func '' U, GaugeZeroRelated d x y → x = y) :
    R_eq ϕA U = R_zero d ϕA U ∧ R_eq ϕB U = R_zero d ϕB U := by
  constructor
  · ext ⟨x, y⟩
    simp only [R_eq, R_zero, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hy, h⟩
      refine ⟨hx, hy, ?_⟩
      intro i
      rw [h]
      exact hd_refl i _
    · rintro ⟨hx, hy, hzero⟩
      refine ⟨hx, hy, ?_⟩
      exact hsepA (ϕA.func x) (Set.mem_image_of_mem _ hx) (ϕA.func y) (Set.mem_image_of_mem _ hy) hzero
  · ext ⟨x, y⟩
    simp only [R_eq, R_zero, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hy, h⟩
      refine ⟨hx, hy, ?_⟩
      intro i
      rw [h]
      exact hd_refl i _
    · rintro ⟨hx, hy, hzero⟩
      refine ⟨hx, hy, ?_⟩
      exact hsepB (ϕB.func x) (Set.mem_image_of_mem _ hx) (ϕB.func y) (Set.mem_image_of_mem _ hy) hzero

/-- CH03-P09-01: 注（纤维包含的传递）：固定公共域的纤维预序自反、传递 -/
theorem prop_3_9_refl_trans (U : Set X) :
    (∀ ϕ : Operator X bot, fiber_preorder d U ϕ ϕ) ∧
    (∀ ϕA ϕB ϕC : Operator X bot, fiber_preorder d U ϕA ϕB → fiber_preorder d U ϕB ϕC → fiber_preorder d U ϕA ϕC) := by
  constructor
  · intro ϕ
    exact le_rfl
  · intro ϕA ϕB ϕC hAB hBC
    exact Set.Subset.trans hAB hBC

/-- CH03-P09-02: 注（纤维包含的传递）：任意有限链任意两层的关系包含 -/
theorem prop_3_9_chain (U : Set X) (ϕs : List (Operator X bot))
    (hchain : ∀ k : ℕ, (hk : k + 1 < ϕs.length) →
      fiber_preorder d U (ϕs.get ⟨k, Nat.lt_of_succ_lt hk⟩) (ϕs.get ⟨k + 1, hk⟩)) :
    ∀ a b : ℕ, (ha : a < ϕs.length) → (hb : b < ϕs.length) → a ≤ b →
      R_zero d (ϕs.get ⟨a, ha⟩) U ⊆ R_zero d (ϕs.get ⟨b, hb⟩) U := by
  intro a b ha hb hab
  induction' hdiff : b - a with n ih generalizing a b
  · have hab_eq : a = b := by omega
    subst hab_eq
    exact le_rfl
  · have ha_lt_b : a < b := by omega
    have ha_succ : a + 1 < ϕs.length := lt_of_le_of_lt (by omega) hb
    have hstep := hchain a ha_succ
    have hdiff_succ : b - (a + 1) = n := by omega
    have hrest := ih (a + 1) b ha_succ hb (by omega) hdiff_succ
    exact Set.Subset.trans hstep hrest

/-- CH03-P09-03: 注（纤维包含的传递）：链中某一步严格包含推出端点严格包含，给出差集见证 -/
theorem prop_3_9_strict (U : Set X) (ϕs : List (Operator X bot))
    (hchain : ∀ k : ℕ, (hk : k + 1 < ϕs.length) →
      fiber_preorder d U (ϕs.get ⟨k, Nat.lt_of_succ_lt hk⟩) (ϕs.get ⟨k + 1, hk⟩))
    (r : ℕ) (hr : r + 1 < ϕs.length)
    (hstrict : R_zero d (ϕs.get ⟨r, Nat.lt_of_succ_lt hr⟩) U ⊂ R_zero d (ϕs.get ⟨r + 1, hr⟩) U)
    (h_nonempty : ϕs.length > 0) :
    R_zero d (ϕs.get ⟨0, h_nonempty⟩) U ⊂ R_zero d (ϕs.get ⟨ϕs.length - 1, Nat.sub_lt h_nonempty (by decide)⟩) U ∧
    ∃ p, p ∈ R_zero d (ϕs.get ⟨ϕs.length - 1, Nat.sub_lt h_nonempty (by decide)⟩) U \ R_zero d (ϕs.get ⟨0, h_nonempty⟩) U := by
  obtain ⟨p, hp_in, hp_not⟩ := Set.exists_of_ssubset hstrict
  have h0_r := prop_3_9_chain d U ϕs hchain 0 r h_nonempty (Nat.lt_of_succ_lt hr) (by omega)
  have hr1_last := prop_3_9_chain d U ϕs hchain (r + 1) (ϕs.length - 1) hr (Nat.sub_lt h_nonempty (by decide)) (by omega)
  have hp_last : p ∈ R_zero d (ϕs.get ⟨ϕs.length - 1, Nat.sub_lt h_nonempty (by decide)⟩) U := hr1_last hp_in
  have hp_not_0 : p ∉ R_zero d (ϕs.get ⟨0, h_nonempty⟩) U := fun hp0 => hp_not (h0_r hp0)
  have hp_diff : p ∈ R_zero d (ϕs.get ⟨ϕs.length - 1, Nat.sub_lt h_nonempty (by decide)⟩) U \ R_zero d (ϕs.get ⟨0, h_nonempty⟩) U :=
    ⟨hp_last, hp_not_0⟩
  have h0_last := prop_3_9_chain d U ϕs hchain 0 (ϕs.length - 1) h_nonempty (Nat.sub_lt h_nonempty (by decide)) (by omega)
  refine ⟨⟨h0_last, ?_⟩, ⟨p, hp_diff⟩⟩
  rintro h_sub
  exact hp_not_0 (h_sub hp_last)

end OperatorLocalDegeneracy
