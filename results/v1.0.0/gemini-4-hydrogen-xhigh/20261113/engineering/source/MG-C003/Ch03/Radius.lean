import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_01_foundations.operator_space
import Ch03.Partition
import Ch03.Fiber
import Mathlib.Tactic

namespace Ch03

open formal_oet.vol_01.ch_01_foundations

section ZeroingRadiusDefs

variable {X I : Type} {bot : X}

/-- 给定基点 `y ∈ U` 的合法有限正零化半径条件。 -/
def IsAdmissibleZeroRadius (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal)
    (U : Set X) (y : X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ball d_in y r ∩ U ⊆ { x ∈ U | d_out (ϕ.func x) (ϕ.func y) = 0 }

/-- **定义（点态零化内切半径）**：`r^N_{ϕ, d_in, d_out}(y | U)`。 -/
noncomputable def pointwiseZeroRadius (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal)
    (U : Set X) (y : X) : ENNReal :=
  ⨆ (r : ENNReal) (_ : IsAdmissibleZeroRadius ϕ d_in d_out U y r), r

/-- 子族输出情形的点态零化半径 `r^N_{ϕ, i, J}(y | U)`。 -/
noncomputable def pointwiseZeroRadiusSubfamily (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) (y : X) : ENNReal :=
  pointwiseZeroRadius ϕ (d i) (subfamily_pseudometric d J) U y

/-- 单输出分量情形的点态零化半径 `r^N_{ϕ, i, j}(y | U)`。 -/
noncomputable def pointwiseZeroRadiusComp (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i j : I) (U : Set X) (y : X) : ENNReal :=
  pointwiseZeroRadius ϕ (d i) (d j) U y

/-- 全域点态零化半径 `r^N_{ϕ, d_in, d_out}(y)`。 -/
noncomputable def pointwiseZeroRadius_global (ϕ : Operator X bot)
    (d_in d_out : X → X → ENNReal) (y : X) : ENNReal :=
  pointwiseZeroRadius ϕ d_in d_out (dom ϕ) y

/-- **定义（指定基点集上的统一零化半径）**：`\underline{r}^N_{ϕ, d_in, d_out}(A | U)`。 -/
noncomputable def uniformZeroRadiusOn (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal)
    (A U : Set X) : ENNReal :=
  ⨅ (y : X) (_ : y ∈ A), pointwiseZeroRadius ϕ d_in d_out U y

/-- 受限域自身的统一零化半径 `\underline{r}^N_{ϕ, d_in, d_out}|_U`。 -/
noncomputable def uniformZeroRadius (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal)
    (U : Set X) : ENNReal :=
  uniformZeroRadiusOn ϕ d_in d_out U U

/-- 子族输出情形的统一零化半径 `\underline{r}^N_{ϕ, i, J}|_U`。 -/
noncomputable def uniformZeroRadiusSubfamily (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) : ENNReal :=
  uniformZeroRadius ϕ (d i) (subfamily_pseudometric d J) U

/-- 单分量情形的统一零化半径 `\underline{r}^N_{ϕ, i, j}|_U`。 -/
noncomputable def uniformZeroRadiusComp (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i j : I) (U : Set X) : ENNReal :=
  uniformZeroRadius ϕ (d i) (d j) U

/-- 全域统一零化半径 `\underline{r}^N_{ϕ, d_in, d_out}`。 -/
noncomputable def uniformZeroRadius_global (ϕ : Operator X bot)
    (d_in d_out : X → X → ENNReal) : ENNReal :=
  uniformZeroRadius ϕ d_in d_out (dom ϕ)

/-- **定义（零化矩阵）**：`[N(ϕ)|_U]_{ji} := \underline{r}^N_{ϕ, i, j}|_U`（行 `j` 为输出，列 `i` 为输入）。 -/
noncomputable def zeroingMatrix (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (U : Set X) : I → I → ENNReal :=
  fun j i => uniformZeroRadiusComp d ϕ i j U

/-- 全域零化矩阵 `N(ϕ)`。 -/
noncomputable def zeroingMatrix_global (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) : I → I → ENNReal :=
  zeroingMatrix d ϕ (dom ϕ)

lemma pointwiseZeroRadiusSubfamily_singleton (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i j : I) (U : Set X) (y : X) :
    pointwiseZeroRadiusSubfamily d ϕ i {j} U y = pointwiseZeroRadiusComp d ϕ i j U y := by
  simp [pointwiseZeroRadiusSubfamily, pointwiseZeroRadiusComp, subfamily_pseudometric_singleton]

lemma uniformZeroRadiusSubfamily_singleton (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i j : I) (U : Set X) :
    uniformZeroRadiusSubfamily d ϕ i {j} U = uniformZeroRadiusComp d ϕ i j U := by
  simp [uniformZeroRadiusSubfamily, uniformZeroRadiusComp, uniformZeroRadius,
    uniformZeroRadiusOn, subfamily_pseudometric_singleton]

lemma output_zero_set_eq_compFiber (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (J : Set I) (U : Set X) (y : X) :
    { x ∈ U | subfamily_pseudometric d J (ϕ.func x) (ϕ.func y) = 0 } =
      compFiber d ϕ J (ϕ.func y) U := rfl

lemma lt_pointwiseZeroRadius_iff (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal)
    (U : Set X) (y : X) (s : ENNReal) :
    s < pointwiseZeroRadius ϕ d_in d_out U y ↔
      ∃ r : ENNReal, s < r ∧ IsAdmissibleZeroRadius ϕ d_in d_out U y r := by
  unfold pointwiseZeroRadius
  constructor
  · intro hs
    rw [lt_iSup_iff] at hs
    rcases hs with ⟨r, hr⟩
    rw [lt_iSup_iff] at hr
    rcases hr with ⟨hadm, hsr⟩
    exact ⟨r, hsr, hadm⟩
  · rintro ⟨r, hsr, hadm⟩
    exact lt_of_lt_of_le hsr (le_iSup_of_le r (le_iSup_of_le hadm le_rfl))

lemma le_pointwiseZeroRadius_of_admissible (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal)
    (U : Set X) (y : X) (r : ENNReal)
    (hadm : IsAdmissibleZeroRadius ϕ d_in d_out U y r) :
    r ≤ pointwiseZeroRadius ϕ d_in d_out U y :=
  le_iSup_of_le r (le_iSup_of_le hadm le_rfl)

lemma isAdmissible_mono_radius (ϕ : Operator X bot) (d_in d_out : X → X → ENNReal)
    (U : Set X) (y : X) {r r' : ENNReal}
    (hr'_pos : 0 < r') (hr'r : r' ≤ r)
    (hadm : IsAdmissibleZeroRadius ϕ d_in d_out U y r) :
    IsAdmissibleZeroRadius ϕ d_in d_out U y r' := by
  refine ⟨hr'_pos, lt_of_le_of_lt hr'r hadm.2.1, ?_⟩
  intro x ⟨hxball, hxU⟩
  apply hadm.2.2
  exact ⟨lt_of_lt_of_le hxball hr'r, hxU⟩

lemma pointwiseZeroRadius_eq_top_of_forall_pos (ϕ : Operator X bot)
    (d_in d_out : X → X → ENNReal) (U : Set X) (y : X)
    (hall : ∀ r : ENNReal, 0 < r → r < ⊤ → IsAdmissibleZeroRadius ϕ d_in d_out U y r) :
    pointwiseZeroRadius ϕ d_in d_out U y = ⊤ := by
  by_contra hne
  have hlt_top : pointwiseZeroRadius ϕ d_in d_out U y < ⊤ := lt_top_iff_ne_top.mpr hne
  let r : ENNReal := pointwiseZeroRadius ϕ d_in d_out U y + 1
  have hr_pos : 0 < r := by positivity
  have hr_fin : r < ⊤ := ENNReal.add_lt_top.mpr ⟨hlt_top, ENNReal.one_lt_top⟩
  have hlt : pointwiseZeroRadius ϕ d_in d_out U y < r :=
    ENNReal.lt_add_right hne one_ne_zero
  have hle := le_pointwiseZeroRadius_of_admissible ϕ d_in d_out U y r (hall r hr_pos hr_fin)
  exact not_lt_of_ge hle hlt

end ZeroingRadiusDefs

section RadiusPropositions

variable {X I : Type} {bot : X}

/-- **命题 3.8 (i-a)**：输出子族全为常值分量时，每个像目标的计算纤维均为 `U`。 -/
theorem prop_3_8_const_fiber (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (J : Set I) (U : Set X) (_hJ : J.Nonempty) (_hU : U ⊆ dom ϕ)
    (hconst : J ⊆ I_const d ϕ U) :
    ∀ y ∈ U, compFiber d ϕ J (ϕ.func y) U = U := by
  intro y hy
  ext x
  simp only [compFiber, Set.mem_setOf_eq, and_iff_left_iff_imp]
  intro hx
  rw [subfamily_pseudometric_eq_zero_iff]
  intro j hj
  exact hconst hj x hx y hy

/-- **命题 3.8 (i-b)**：输出子族全为常值分量时，任一输入分量的点态与统一零化半径均为 `+∞`。 -/
theorem prop_3_8_const_radius_top (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (J : Set I) (U : Set X) (_hUne : U.Nonempty) (hJ : J.Nonempty) (hU : U ⊆ dom ϕ)
    (hconst : J ⊆ I_const d ϕ U) :
    ∀ i : I,
      (∀ y ∈ U, pointwiseZeroRadiusSubfamily d ϕ i J U y = ⊤) ∧
      uniformZeroRadiusSubfamily d ϕ i J U = ⊤ := by
  intro i
  have hpt : ∀ y ∈ U, pointwiseZeroRadiusSubfamily d ϕ i J U y = ⊤ := by
    intro y hy
    apply pointwiseZeroRadius_eq_top_of_forall_pos
    intro r hr_pos hr_fin
    refine ⟨hr_pos, hr_fin, ?_⟩
    intro x ⟨_, hxU⟩
    refine ⟨hxU, ?_⟩
    have hfib := prop_3_8_const_fiber d ϕ J U hJ hU hconst y hy
    have hmem : x ∈ compFiber d ϕ J (ϕ.func y) U := by rw [hfib]; exact hxU
    exact hmem.2
  refine ⟨hpt, ?_⟩
  unfold uniformZeroRadiusSubfamily uniformZeroRadius uniformZeroRadiusOn
  apply le_antisymm le_top
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  exact le_of_eq (hpt y hy).symm

/-- **命题 3.9 (i)**：恒等分量以 `ϕ(y)` 为目标的计算纤维等于 `y` 的输入零距类。 -/
theorem prop_3_9_id_fiber (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (y : X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom ϕ) (_hy : y ∈ U) (hi : i ∈ I_id d ϕ U) :
    compFiber_single d ϕ i (ϕ.func y) U = { x ∈ U | d i x y = 0 } := by
  rw [compFiber_single_eq]
  ext x
  simp only [Set.mem_setOf_eq]
  refine and_congr_right fun hx => ?_
  rw [prop_3_1_id_isometry d ϕ U i hd hU hi x hx y _hy]

/-- **命题 3.9 (ii)**：恒等分量在有限正开球内仅零距时，点态零化半径至少为该半径且严格为正。 -/
theorem prop_3_9_id_radius_ge (d : I → X → X → ENNReal) (ϕ : Operator X bot)
    (U : Set X) (y : X) (i : I) (r₀ : ENNReal)
    (hd : ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom ϕ) (hy : y ∈ U) (hi : i ∈ I_id d ϕ U)
    (hr₀_pos : 0 < r₀) (hr₀_fin : r₀ < ⊤)
    (hball : ball (d i) y r₀ ∩ U ⊆ { x ∈ U | d i x y = 0 }) :
    r₀ ≤ pointwiseZeroRadiusComp d ϕ i i U y ∧ 0 < pointwiseZeroRadiusComp d ϕ i i U y := by
  have hadm : IsAdmissibleZeroRadius ϕ (d i) (d i) U y r₀ := by
    refine ⟨hr₀_pos, hr₀_fin, ?_⟩
    intro x hx
    have hmem := hball hx
    refine ⟨hmem.1, ?_⟩
    rw [prop_3_1_id_isometry d ϕ U i hd hU hi x hmem.1 y hy]
    exact hmem.2
  have hle := le_pointwiseZeroRadius_of_admissible ϕ (d i) (d i) U y r₀ hadm
  exact ⟨hle, lt_of_lt_of_le hr₀_pos hle⟩

/-- **命题 3.10 (i-a, Finset 版)**：有限非空输出子族的点态零化半径等于单分量半径最小值。 -/
theorem prop_3_10_pointwise_min_finset (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i : I) (J : Finset I) (hJ : J.Nonempty)
    (U : Set X) (y : X) :
    pointwiseZeroRadiusSubfamily d ϕ i (↑J : Set I) U y =
      J.inf' hJ (fun j => pointwiseZeroRadiusComp d ϕ i j U y) := by
  apply le_antisymm
  · apply Finset.le_inf' hJ
    intro j hj
    unfold pointwiseZeroRadiusSubfamily pointwiseZeroRadiusComp pointwiseZeroRadius
    apply iSup_le
    intro r
    apply iSup_le
    intro hadm
    apply le_pointwiseZeroRadius_of_admissible
    refine ⟨hadm.1, hadm.2.1, ?_⟩
    intro x hx
    have hx' := hadm.2.2 hx
    refine ⟨hx'.1, ?_⟩
    have hle : d j (ϕ.func x) (ϕ.func y) ≤
        subfamily_pseudometric d (↑J : Set I) (ϕ.func x) (ϕ.func y) :=
      le_iSup (fun k : {k // k ∈ (↑J : Set I)} => d k.1 (ϕ.func x) (ϕ.func y))
        ⟨j, Finset.mem_coe.mpr hj⟩
    rw [hx'.2] at hle
    exact le_antisymm hle (zero_le _)
  · by_contra hlt
    rw [not_le] at hlt
    have hchoose : ∀ j : I, j ∈ J →
        ∃ r : ENNReal, pointwiseZeroRadiusSubfamily d ϕ i (↑J : Set I) U y < r ∧
          IsAdmissibleZeroRadius ϕ (d i) (d j) U y r := by
      intro j hj
      have hjlt : pointwiseZeroRadiusSubfamily d ϕ i (↑J : Set I) U y <
          pointwiseZeroRadiusComp d ϕ i j U y :=
        lt_of_lt_of_le hlt (Finset.inf'_le (fun k => pointwiseZeroRadiusComp d ϕ i k U y) hj)
      exact (lt_pointwiseZeroRadius_iff ϕ (d i) (d j) U y _).mp hjlt
    choose r_fn hr_spec using hchoose
    let rmin : ENNReal := J.attach.inf' (Finset.Nonempty.attach hJ) (fun j => r_fn j.1 j.2)
    have hrmin_gt : pointwiseZeroRadiusSubfamily d ϕ i (↑J : Set I) U y < rmin := by
      rw [Finset.lt_inf'_iff]
      intro j _
      exact (hr_spec j.1 j.2).1
    have hrmin_pos : 0 < rmin := lt_of_le_of_lt (zero_le _) hrmin_gt
    rcases hJ with ⟨j₀, hj₀⟩
    have hrmin_le_j₀ : rmin ≤ r_fn j₀ hj₀ :=
      Finset.inf'_le (fun j : {j // j ∈ J} => r_fn j.1 j.2) (Finset.mem_attach J ⟨j₀, hj₀⟩)
    have hrmin_fin : rmin < ⊤ := lt_of_le_of_lt hrmin_le_j₀ (hr_spec j₀ hj₀).2.2.1
    have hadm : IsAdmissibleZeroRadius ϕ (d i) (subfamily_pseudometric d (↑J : Set I)) U y rmin := by
      refine ⟨hrmin_pos, hrmin_fin, ?_⟩
      intro x ⟨hxball, hxU⟩
      refine ⟨hxU, ?_⟩
      rw [subfamily_pseudometric_eq_zero_iff]
      intro j hj
      have hj_mem : j ∈ J := Finset.mem_coe.mp hj
      have hrmin_le_j : rmin ≤ r_fn j hj_mem :=
        Finset.inf'_le (fun k : {k // k ∈ J} => r_fn k.1 k.2) (Finset.mem_attach J ⟨j, hj_mem⟩)
      have hx_in_j := (hr_spec j hj_mem).2.2.2 ⟨lt_of_lt_of_le hxball hrmin_le_j, hxU⟩
      exact hx_in_j.2
    have hle := le_pointwiseZeroRadius_of_admissible ϕ (d i)
      (subfamily_pseudometric d (↑J : Set I)) U y rmin hadm
    exact not_lt_of_ge hle hrmin_gt

/-- **命题 3.10 (i-b, `Set.Finite` 版)**：有限非空输出子族的点态零化半径等于单分量半径的下确界/最小值。 -/
theorem prop_3_10_pointwise_min (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i : I) (J : Set I) (hJ_fin : J.Finite) (hJ_ne : J.Nonempty)
    (U : Set X) (y : X) :
    pointwiseZeroRadiusSubfamily d ϕ i J U y =
      ⨅ j : {j // j ∈ J}, pointwiseZeroRadiusComp d ϕ i j.1 U y := by
  classical
  let Jf : Finset I := hJ_fin.toFinset
  have hJf_coe : (↑Jf : Set I) = J := hJ_fin.coe_toFinset
  have hJf_ne : Jf.Nonempty := by
    rcases hJ_ne with ⟨j, hj⟩
    exact ⟨j, hJ_fin.mem_toFinset.mpr hj⟩
  have hmin := prop_3_10_pointwise_min_finset d ϕ i Jf hJf_ne U y
  rw [hJf_coe] at hmin
  rw [hmin]
  apply le_antisymm
  · apply le_iInf
    intro j
    exact Finset.inf'_le _ (hJ_fin.mem_toFinset.mpr j.2)
  · apply Finset.le_inf' hJf_ne
    intro j hj
    exact iInf_le (fun k : {k // k ∈ J} => pointwiseZeroRadiusComp d ϕ i k.1 U y)
      ⟨j, hJ_fin.mem_toFinset.mp hj⟩

/-- **命题 3.10 (ii)**：有限非空输出子族的统一零化半径等于零化矩阵对应分量条目的最小值。 -/
theorem prop_3_10_uniform_min (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i : I) (J : Set I) (hJ_fin : J.Finite) (hJ_ne : J.Nonempty)
    (U : Set X) :
    uniformZeroRadiusSubfamily d ϕ i J U =
      ⨅ j : {j // j ∈ J}, zeroingMatrix d ϕ U j.1 i := by
  have hpt : ∀ y, pointwiseZeroRadiusSubfamily d ϕ i J U y =
      ⨅ j : {j // j ∈ J}, pointwiseZeroRadiusComp d ϕ i j.1 U y :=
    fun y => prop_3_10_pointwise_min d ϕ i J hJ_fin hJ_ne U y
  unfold uniformZeroRadiusSubfamily uniformZeroRadius uniformZeroRadiusOn
  calc
    ⨅ y, ⨅ (_ : y ∈ U), pointwiseZeroRadius ϕ (d i) (subfamily_pseudometric d J) U y
        = ⨅ y, ⨅ (_ : y ∈ U), ⨅ j : {j // j ∈ J}, pointwiseZeroRadiusComp d ϕ i j.1 U y :=
          iInf_congr fun y => iInf_congr fun _ => hpt y
    _ = ⨅ j : {j // j ∈ J}, zeroingMatrix d ϕ U j.1 i := by
          rw [iInf_congr fun y => iInf_comm, iInf_comm]
          rfl

/-- Finset 形式的统一零化半径分量最小值公式。 -/
theorem prop_3_10_uniform_min_finset (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i : I) (J : Finset I) (hJ : J.Nonempty) (U : Set X) :
    uniformZeroRadiusSubfamily d ϕ i (↑J : Set I) U =
      J.inf' hJ (fun j => zeroingMatrix d ϕ U j i) := by
  rw [prop_3_10_uniform_min d ϕ i (↑J : Set I) J.finite_toSet hJ U]
  apply le_antisymm
  · apply Finset.le_inf' hJ
    intro j hj
    exact iInf_le (fun k : {k // k ∈ (↑J : Set I)} => zeroingMatrix d ϕ U k.1 i)
      ⟨j, Finset.mem_coe.mpr hj⟩
  · apply le_iInf
    intro j
    exact Finset.inf'_le (fun k => zeroingMatrix d ϕ U k i) (Finset.mem_coe.mp j.2)

/-- **命题 3.10 (iii)**：输出子族扩大时统一零化半径反单调。 -/
theorem prop_3_10_antitone_subfamily (d : I → X → X → ENNReal)
    (ϕ : Operator X bot) (i : I) (J K : Set I) (_hJ : J.Nonempty) (hJK : J ⊆ K)
    (U : Set X) :
    uniformZeroRadiusSubfamily d ϕ i K U ≤ uniformZeroRadiusSubfamily d ϕ i J U := by
  unfold uniformZeroRadiusSubfamily uniformZeroRadius uniformZeroRadiusOn
  apply iInf_mono
  intro y
  apply iInf_mono
  intro _
  unfold pointwiseZeroRadius
  apply iSup_le
  intro r
  apply iSup_le
  intro hadm
  apply le_pointwiseZeroRadius_of_admissible
  refine ⟨hadm.1, hadm.2.1, ?_⟩
  intro x hx
  have hx' := hadm.2.2 hx
  have hx'2 := hx'.2
  refine ⟨hx'.1, ?_⟩
  rw [subfamily_pseudometric_eq_zero_iff] at hx'2 ⊢
  intro j hj
  exact hx'2 j (hJK hj)

/-- **命题 3.11 (i)**：纤维成员条件直接给出输出零距。 -/
theorem prop_3_11_cutoff_fiber (d : I → X → X → ENNReal)
    (ϕ₂ : Operator X bot) (U₂ : Set X) (j : I) (y y' : X)
    (hdj : ExtendedPseudoMetric X bot (d j))
    (_hy : y ∈ U₂) (hy' : y' ∈ compFiber_single d ϕ₂ j (ϕ₂.func y) U₂) :
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  rw [compFiber_single_eq] at hy'
  rw [hdj.symm]
  exact hy'.2

/-- **命题 3.11 (ii)**：输入距离严格小于点态零化半径时输出必零距。 -/
theorem prop_3_11_cutoff_radius (d : I → X → X → ENNReal)
    (ϕ₂ : Operator X bot) (U₂ : Set X) (i j : I) (y y' : X)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (_hy : y ∈ U₂) (hy' : y' ∈ U₂)
    (hdist : d i y y' < pointwiseZeroRadiusComp d ϕ₂ i j U₂ y) :
    d j (ϕ₂.func y) (ϕ₂.func y') = 0 := by
  rcases (lt_pointwiseZeroRadius_iff ϕ₂ (d i) (d j) U₂ y _).mp hdist with ⟨ρ, hlt, hadm⟩
  have hy'_ball : y' ∈ ball (d i) y ρ ∩ U₂ := by
    refine ⟨?_, hy'⟩
    dsimp [ball]
    rw [hdi.symm]
    exact hlt
  have hmem := hadm.2.2 hy'_ball
  rw [hdj.symm]
  exact hmem.2

/-- **命题 3.11 (iii)**：复合算子在下游指定像域上的纤维截断判据。 -/
theorem prop_3_11_cutoff_comp (d : I → X → X → ENNReal)
    (ϕ₁ ϕ₂ : Operator X bot) (U₂ : Set X) (j : I) (x x' : X)
    (hdj : ExtendedPseudoMetric X bot (d j))
    (_hU₂ : U₂ ⊆ dom ϕ₂) (_hx : x ∈ dom ϕ₁) (_hx' : x' ∈ dom ϕ₁)
    (hy : ϕ₁.func x ∈ U₂)
    (hy' : ϕ₁.func x' ∈ compFiber_single d ϕ₂ j (ϕ₂.func (ϕ₁.func x)) U₂) :
    d j ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func x') = 0 :=
  prop_3_11_cutoff_fiber d ϕ₂ U₂ j (ϕ₁.func x) (ϕ₁.func x') hdj hy hy'

/-- **命题 3.12 (i)**：下游算子在实际像域保持零距时，复合统一零化半径不低于上游对应条目。 -/
theorem prop_3_12_comp_zero_preserve (d : I → X → X → ENNReal)
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i j l : I)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (_hdj : ExtendedPseudoMetric X bot (d j))
    (hdl : ExtendedPseudoMetric X bot (d l))
    (_hUne : U.Nonempty) (_hU : U ⊆ dom (ϕ₂ * ϕ₁))
    (hpreserve : ∀ y ∈ ϕ₁.func '' U, ∀ y' ∈ ϕ₁.func '' U,
      d l y y' = 0 → d j (ϕ₂.func y) (ϕ₂.func y') = 0) :
    zeroingMatrix d ϕ₁ U l i ≤ zeroingMatrix d (ϕ₂ * ϕ₁) U j i := by
  unfold zeroingMatrix uniformZeroRadiusComp uniformZeroRadius uniformZeroRadiusOn
  apply iInf_mono
  intro x
  apply iInf_mono
  intro hx
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨r, hr_gt, hr_lt⟩ := exists_between hlt
  have hr_pos : 0 < r := lt_of_le_of_lt (zero_le _) hr_gt
  have hr_lt_pt : r < pointwiseZeroRadiusComp d ϕ₁ i l U x :=
    lt_of_lt_of_le hr_lt le_rfl
  have hr_fin : r < ⊤ := lt_of_lt_of_le hr_lt le_top
  have hadm : IsAdmissibleZeroRadius (ϕ₂ * ϕ₁) (d i) (d j) U x r := by
    refine ⟨hr_pos, hr_fin, ?_⟩
    intro x' ⟨hx'_ball, hx'U⟩
    refine ⟨hx'U, ?_⟩
    have hd_lt : d i x x' < pointwiseZeroRadiusComp d ϕ₁ i l U x := by
      rw [hdi.symm]
      exact lt_trans hx'_ball hr_lt_pt
    have hl_zero := prop_3_11_cutoff_radius d ϕ₁ U i l x x' hdi hdl hx hx'U hd_lt
    have hl_zero' : d l (ϕ₁.func x') (ϕ₁.func x) = 0 := by
      rw [hdl.symm]; exact hl_zero
    exact hpreserve _ ⟨x', hx'U, rfl⟩ _ ⟨x, hx, rfl⟩ hl_zero'
  have hle := le_pointwiseZeroRadius_of_admissible (ϕ₂ * ϕ₁) (d i) (d j) U x r hadm
  exact not_lt_of_ge hle hr_gt

/-- **命题 3.12 (ii)**：经有限正单通道 Lip 上界拉回下游统一零化半径（统一处理 0 与无穷）。 -/
theorem prop_3_12_comp_lip_pullback (d : I → X → X → ENNReal)
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (i j l : I) (L : ENNReal)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hdj : ExtendedPseudoMetric X bot (d j))
    (hdl : ExtendedPseudoMetric X bot (d l))
    (_hUne : U.Nonempty) (_hU : U ⊆ dom (ϕ₂ * ϕ₁))
    (hL_pos : 0 < L) (hL_fin : L < ⊤)
    (hLip : ∀ x ∈ U, ∀ x' ∈ U, d l (ϕ₁.func x) (ϕ₁.func x') ≤ L * d i x x') :
    zeroingMatrix d ϕ₂ (ϕ₁.func '' U) j l / L ≤ zeroingMatrix d (ϕ₂ * ϕ₁) U j i := by
  unfold zeroingMatrix uniformZeroRadiusComp uniformZeroRadius uniformZeroRadiusOn
  apply le_iInf
  intro x
  apply le_iInf
  intro hx
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨r, hr_gt, hr_lt⟩ := exists_between hlt
  have hr_pos : 0 < r := lt_of_le_of_lt (zero_le _) hr_gt
  have hr_fin : r < ⊤ := lt_of_lt_of_le hr_lt le_top
  have hLr_lt : L * r <
      ⨅ y, ⨅ (_ : y ∈ ϕ₁.func '' U), pointwiseZeroRadiusComp d ϕ₂ l j (ϕ₁.func '' U) y := by
    have hL_ne_zero : L ≠ 0 := ne_of_gt hL_pos
    have hL_ne_top : L ≠ ⊤ := ne_of_lt hL_fin
    by_cases hNtop :
        (⨅ y, ⨅ (_ : y ∈ ϕ₁.func '' U), pointwiseZeroRadiusComp d ϕ₂ l j (ϕ₁.func '' U) y) = ⊤
    · rw [hNtop]
      exact ENNReal.mul_lt_top hL_fin hr_fin
    · calc
        L * r = r * L := mul_comm L r
        _ < ((⨅ y, ⨅ (_ : y ∈ ϕ₁.func '' U),
            pointwiseZeroRadiusComp d ϕ₂ l j (ϕ₁.func '' U) y) / L) * L :=
          ENNReal.mul_lt_mul_left hL_ne_zero hL_ne_top hr_lt
        _ = L * ((⨅ y, ⨅ (_ : y ∈ ϕ₁.func '' U),
            pointwiseZeroRadiusComp d ϕ₂ l j (ϕ₁.func '' U) y) / L) := mul_comm _ L
        _ = ⨅ y, ⨅ (_ : y ∈ ϕ₁.func '' U), pointwiseZeroRadiusComp d ϕ₂ l j (ϕ₁.func '' U) y :=
          ENNReal.mul_div_cancel hL_ne_zero hL_ne_top
  have hadm : IsAdmissibleZeroRadius (ϕ₂ * ϕ₁) (d i) (d j) U x r := by
    refine ⟨hr_pos, hr_fin, ?_⟩
    intro x' ⟨hx'_ball, hx'U⟩
    refine ⟨hx'U, ?_⟩
    have hd_le_Lr : d l (ϕ₁.func x) (ϕ₁.func x') < L * r := by
      have h1 : d l (ϕ₁.func x) (ϕ₁.func x') ≤ L * d i x x' := hLip x hx x' hx'U
      have h2 : L * d i x x' < L * r := by
        rw [hdi.symm, mul_comm L, mul_comm L r]
        exact ENNReal.mul_lt_mul_left (ne_of_gt hL_pos) (ne_of_lt hL_fin) hx'_ball
      exact lt_of_le_of_lt h1 h2
    have hd_lt_pt : d l (ϕ₁.func x) (ϕ₁.func x') <
        pointwiseZeroRadiusComp d ϕ₂ l j (ϕ₁.func '' U) (ϕ₁.func x) := by
      have hd_lt_inf : d l (ϕ₁.func x) (ϕ₁.func x') <
          ⨅ y, ⨅ (_ : y ∈ ϕ₁.func '' U), pointwiseZeroRadiusComp d ϕ₂ l j (ϕ₁.func '' U) y :=
        lt_trans hd_le_Lr hLr_lt
      exact lt_of_lt_of_le hd_lt_inf
        (iInf_le_of_le (ϕ₁.func x) (iInf_le_of_le ⟨x, hx, rfl⟩ le_rfl))
    have hj_zero := prop_3_11_cutoff_radius d ϕ₂ (ϕ₁.func '' U) l j
      (ϕ₁.func x) (ϕ₁.func x') hdl hdj ⟨x, hx, rfl⟩ ⟨x', hx'U, rfl⟩ hd_lt_pt
    rw [hdj.symm]
    exact hj_zero
  have hle := le_pointwiseZeroRadius_of_admissible (ϕ₂ * ϕ₁) (d i) (d j) U x r hadm
  exact not_lt_of_ge hle hr_gt

end RadiusPropositions

section Counterexamples33

open formal_oet.vol_01.ch_01_foundations

/-- 实数直线并吸收元 `ℝ ⊔ {bot}` 上的通常绝对值距离。 -/
noncomputable def realAbsDist : Option ℝ → Option ℝ → ENNReal
  | none, none => 0
  | none, some _ => ⊤
  | some _, none => ⊤
  | some x, some y => ENNReal.ofReal |x - y|

lemma realAbsDist_is_extended : ExtendedPseudoMetric (Option ℝ) none realAbsDist := by
  refine
    { nonabsorbing := ⟨some 0, by simp⟩
      dist_self := by
        intro x
        cases x with
        | none => rfl
        | some r => simp [realAbsDist]
      symm := by
        intro x y
        cases x <;> cases y <;> simp [realAbsDist, abs_sub_comm]
      triangle := by
        intro x y z
        cases x with
        | none =>
            cases y with
            | none => simp [realAbsDist]
            | some _ => simp [realAbsDist]
        | some a =>
            cases y with
            | none => simp [realAbsDist]
            | some b =>
                cases z with
                | none => simp [realAbsDist]
                | some c =>
                    simp only [realAbsDist]
                    calc
                      ENNReal.ofReal |a - c|
                          ≤ ENNReal.ofReal (|a - b| + |b - c|) :=
                            ENNReal.ofReal_le_ofReal (abs_sub_le a b c)
                      _ = ENNReal.ofReal |a - b| + ENNReal.ofReal |b - c| :=
                            ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      isolate_bot := by
        intro x hx
        cases x with
        | none => exact False.elim (hx rfl)
        | some _ => rfl }

/-- 反例 3.1 中的阶跃算子：`x < 0 ↦ 0`，`x ≥ 0 ↦ 1`，`bot ↦ bot`。 -/
noncomputable def stepOp : Operator (Option ℝ) none where
  func
    | none => none
    | some x => if x < 0 then some 0 else some 1
  preserves_bot := rfl

/-- 反例 3.1 的评估域 `U = [-1, 0) ∪ (0, 1]`。 -/
def U_ce31 : Set (Option ℝ) :=
  { p | ∃ x : ℝ, p = some x ∧ ((-1 ≤ x ∧ x < 0) ∨ (0 < x ∧ x ≤ 1)) }

/-- **反例 3.1 (i)**：合法结构、非空性与评估域条件验证。 -/
theorem ce31_valid :
    ExtendedPseudoMetric (Option ℝ) none realAbsDist ∧
    U_ce31.Nonempty ∧
    U_ce31 ⊆ dom stepOp := by
  refine ⟨realAbsDist_is_extended, ⟨some 1, 1, rfl, Or.inr ⟨zero_lt_one, le_rfl⟩⟩, ?_⟩
  rintro p ⟨x, rfl, _⟩
  simp only [dom, Set.mem_setOf_eq, stepOp]
  split_ifs <;> simp

/-- **反例 3.1 (ii-a)**：每个 `y = some t ∈ U_ce31` 的合法有限正半径恰为 `(0, |t|]`。 -/
theorem ce31_admissible_iff (t : ℝ) (ht : (-1 ≤ t ∧ t < 0) ∨ (0 < t ∧ t ≤ 1)) (r : ENNReal) :
    IsAdmissibleZeroRadius stepOp realAbsDist realAbsDist U_ce31 (some t) r ↔
      0 < r ∧ r ≤ ENNReal.ofReal |t| := by
  have ht_ne : t ≠ 0 := by
    rcases ht with ⟨_, hlt⟩ | ⟨hgt, _⟩ <;> linarith
  have habs_pos : 0 < |t| := abs_pos.mpr ht_ne
  constructor
  · intro hadm
    refine ⟨hadm.1, ?_⟩
    by_contra hgt
    rw [not_le] at hgt
    have hr_ne_top : r ≠ ⊤ := ne_of_lt hadm.2.1
    have hlt_real : |t| < r.toReal := by
      have hof : ENNReal.ofReal |t| < ENNReal.ofReal r.toReal := by
        rwa [ENNReal.ofReal_toReal hr_ne_top]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg t)).mp hof
    let δ : ℝ := min (1 / 2) ((r.toReal - |t|) / 2)
    have hδ_pos : 0 < δ := by
      apply lt_min
      · positivity
      · linarith
    have hδ_le_half : δ ≤ 1 / 2 := min_le_left _ _
    have hδ_lt_diff : δ < r.toReal - |t| := by
      have h1 : δ ≤ (r.toReal - |t|) / 2 := min_le_right _ _
      linarith
    rcases ht with ⟨_, ht_neg⟩ | ⟨ht_pos, _⟩
    · have hs_mem : some δ ∈ U_ce31 :=
        ⟨δ, rfl, Or.inr ⟨hδ_pos, by linarith⟩⟩
      have hdist_real : |δ - t| < r.toReal := by
        have hpos_diff : 0 < δ - t := by linarith
        rw [abs_of_pos hpos_diff, abs_of_neg ht_neg] at *
        linarith
      have hs_ball : some δ ∈ ball realAbsDist (some t) r := by
        dsimp [ball, realAbsDist]
        calc
          ENNReal.ofReal |δ - t| < ENNReal.ofReal r.toReal :=
            ENNReal.ofReal_lt_ofReal_iff (lt_trans habs_pos hlt_real) |>.mpr hdist_real
          _ = r := ENNReal.ofReal_toReal hr_ne_top
      have hzero := (hadm.2.2 ⟨hs_ball, hs_mem⟩).2
      have hnot_neg : ¬ δ < 0 := not_lt.mpr (le_of_lt hδ_pos)
      simp [stepOp, hnot_neg, ht_neg, realAbsDist] at hzero
    · have hs_mem : some (-δ) ∈ U_ce31 :=
        ⟨-δ, rfl, Or.inl ⟨by linarith, neg_lt_zero.mpr hδ_pos⟩⟩
      have hdist_real : |-δ - t| < r.toReal := by
        have hneg_diff : -δ - t < 0 := by linarith
        rw [abs_of_neg hneg_diff, abs_of_pos ht_pos] at *
        linarith
      have hs_ball : some (-δ) ∈ ball realAbsDist (some t) r := by
        dsimp [ball, realAbsDist]
        calc
          ENNReal.ofReal |-δ - t| < ENNReal.ofReal r.toReal :=
            ENNReal.ofReal_lt_ofReal_iff (lt_trans habs_pos hlt_real) |>.mpr hdist_real
          _ = r := ENNReal.ofReal_toReal hr_ne_top
      have hzero := (hadm.2.2 ⟨hs_ball, hs_mem⟩).2
      have hnot_pos : ¬ t < 0 := not_lt.mpr (le_of_lt ht_pos)
      have hneg_s : -δ < 0 := neg_lt_zero.mpr hδ_pos
      simp [stepOp, hneg_s, hnot_pos, realAbsDist] at hzero
  · rintro ⟨hr_pos, hr_le⟩
    refine ⟨hr_pos, lt_of_le_of_lt hr_le ENNReal.ofReal_lt_top, ?_⟩
    rintro x ⟨hxball, s, rfl, hs⟩
    refine ⟨⟨s, rfl, hs⟩, ?_⟩
    have hlt_enn : ENNReal.ofReal |s - t| < ENNReal.ofReal |t| :=
      lt_of_lt_of_le hxball hr_le
    have hlt_abs : |s - t| < |t| :=
      (ENNReal.ofReal_lt_ofReal_iff habs_pos).mp hlt_enn
    rcases ht with ⟨_, ht_neg⟩ | ⟨ht_pos, _⟩
    · rw [abs_of_neg ht_neg] at hlt_abs
      have hs_neg : s < 0 := by
        have h := le_trans (le_abs_self (s - t)) hlt_abs.le
        linarith [lt_of_le_of_lt (le_abs_self (s - t)) hlt_abs]
      simp [stepOp, hs_neg, ht_neg, realAbsDist]
    · rw [abs_of_pos ht_pos] at hlt_abs
      have hs_pos : 0 < s := by
        have h := lt_of_le_of_lt (neg_le_abs (s - t)) hlt_abs
        linarith
      have hns : ¬ s < 0 := not_lt.mpr (le_of_lt hs_pos)
      have hnt : ¬ t < 0 := not_lt.mpr (le_of_lt ht_pos)
      simp [stepOp, hns, hnt, realAbsDist]

/-- **反例 3.1 (ii-b)**：每个 `y ∈ U_ce31` 的点态零化半径等于 `|t| > 0`。 -/
theorem ce31_pointwise_pos :
    ∀ y ∈ U_ce31, ∃ t : ℝ, y = some t ∧
      pointwiseZeroRadius stepOp realAbsDist realAbsDist U_ce31 y = ENNReal.ofReal |t| ∧
      0 < pointwiseZeroRadius stepOp realAbsDist realAbsDist U_ce31 y := by
  rintro y ⟨t, rfl, ht⟩
  have ht_ne : t ≠ 0 := by
    rcases ht with ⟨_, hlt⟩ | ⟨hgt, _⟩ <;> linarith
  have habs_pos : 0 < |t| := abs_pos.mpr ht_ne
  have hpos_enn : 0 < ENNReal.ofReal |t| := ENNReal.ofReal_pos.mpr habs_pos
  have heq : pointwiseZeroRadius stepOp realAbsDist realAbsDist U_ce31 (some t) =
      ENNReal.ofReal |t| := by
    apply le_antisymm
    · unfold pointwiseZeroRadius
      apply iSup₂_le
      intro r hr
      exact ((ce31_admissible_iff t ht r).mp hr).2
    · exact le_pointwiseZeroRadius_of_admissible stepOp realAbsDist realAbsDist U_ce31
        (some t) (ENNReal.ofReal |t|)
        ((ce31_admissible_iff t ht (ENNReal.ofReal |t|)).mpr ⟨hpos_enn, le_rfl⟩)
  exact ⟨t, rfl, heq, heq ▸ hpos_enn⟩

/-- **反例 3.1 (iii)**：同一固定评估域 `U_ce31` 上的统一零化半径为 `0`。 -/
theorem ce31_uniform_zero :
    uniformZeroRadius stepOp realAbsDist realAbsDist U_ce31 = 0 := by
  apply le_antisymm _ (zero_le _)
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε_pos _
  rw [zero_add]
  let t : ℝ := min 1 (ε : ℝ)
  have ht_pos : 0 < t := lt_min zero_lt_one hε_pos
  have ht_le_one : t ≤ 1 := min_le_left _ _
  have ht_mem : some t ∈ U_ce31 := ⟨t, rfl, Or.inr ⟨ht_pos, ht_le_one⟩⟩
  have hpt : pointwiseZeroRadius stepOp realAbsDist realAbsDist U_ce31 (some t) =
      ENNReal.ofReal t := by
    obtain ⟨t', heq_some, hpt_eq, _⟩ := ce31_pointwise_pos (some t) ht_mem
    cases heq_some
    rw [hpt_eq, abs_of_pos ht_pos]
  calc
    uniformZeroRadius stepOp realAbsDist realAbsDist U_ce31
        ≤ pointwiseZeroRadius stepOp realAbsDist realAbsDist U_ce31 (some t) :=
          iInf_le_of_le (some t) (iInf_le_of_le ht_mem le_rfl)
    _ = ENNReal.ofReal t := hpt
    _ ≤ ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = (ε : ENNReal) := ENNReal.ofReal_coe_nnreal

/-- 命题 3.8 (ii) 反例的三点空间 `{bot, a, b}`。 -/
inductive BotAB : Type
  | bot
  | a
  | b
  deriving DecidableEq

/-- 命题 3.8 (ii) 反例的双分量距离：`false` 分量令 `a, b` 距 `⊤`，`true` 分量令 `a, b` 距 `1`。 -/
def ce38Dist : Bool → BotAB → BotAB → ENNReal
  | false, x, y =>
      if x = y then 0
      else ⊤
  | true, x, y =>
      if x = y then 0
      else if x = .bot ∨ y = .bot then ⊤
      else 1

lemma ce38Dist_is_extended : ∀ k : Bool, ExtendedPseudoMetric BotAB .bot (ce38Dist k) := by
  intro k
  refine
    { nonabsorbing := ⟨.a, by decide⟩
      dist_self := by intro x; cases k <;> cases x <;> simp [ce38Dist]
      symm := by intro x y; cases k <;> cases x <;> cases y <;> simp [ce38Dist]
      triangle := by
        intro x y z
        cases k <;> cases x <;> cases y <;> cases z <;> simp [ce38Dist]
      isolate_bot := by
        intro x hx
        cases x
        · exact False.elim (hx rfl)
        all_goals (cases k <;> simp [ce38Dist]) }

def ce38U : Set BotAB := {.a, .b}

/-- **命题 3.8 (ii)**：合法两点无穷输入距离反例（同时覆盖 `i = j` 与 `i ≠ j` 两种情形），
证明 `[N(ϕ)|_U]_{ji} = +∞` 一般不推出 `j ∈ I_const(ϕ | U)`。 -/
theorem prop_3_8_top_not_const_counterexample :
    (∀ k : Bool, ExtendedPseudoMetric BotAB .bot (ce38Dist k)) ∧
    ce38U.Nonempty ∧
    ce38U ⊆ dom (1 : Operator BotAB .bot) ∧
    (zeroingMatrix ce38Dist (1 : Operator BotAB .bot) ce38U false false = ⊤ ∧
      false ∉ I_const ce38Dist (1 : Operator BotAB .bot) ce38U) ∧
    (zeroingMatrix ce38Dist (1 : Operator BotAB .bot) ce38U true false = ⊤ ∧
      true ∉ I_const ce38Dist (1 : Operator BotAB .bot) ce38U) := by
  have hU_ne : ce38U.Nonempty := ⟨.a, Or.inl rfl⟩
  have hU_dom : ce38U ⊆ dom (1 : Operator BotAB .bot) := by
    intro x hx
    rcases hx with rfl | rfl <;> simp [dom]
  have hadm_all : ∀ j : Bool, ∀ y ∈ ce38U, ∀ r : ENNReal, 0 < r → r < ⊤ →
      IsAdmissibleZeroRadius (1 : Operator BotAB .bot) (ce38Dist false) (ce38Dist j)
        ce38U y r := by
    intro j y hy r hr_pos hr_fin
    refine ⟨hr_pos, hr_fin, ?_⟩
    intro x ⟨hxball, hxU⟩
    refine ⟨hxU, ?_⟩
    have hxy : x = y := by
      rcases hxU with rfl | rfl <;> rcases hy with rfl | rfl
      · rfl
      · exfalso; dsimp [ball, ce38Dist] at hxball; exact not_lt_of_ge le_top hxball
      · exfalso; dsimp [ball, ce38Dist] at hxball; exact not_lt_of_ge le_top hxball
      · rfl
    subst hxy
    exact (ce38Dist_is_extended j).dist_self _
  have hmat_top : ∀ j : Bool,
      zeroingMatrix ce38Dist (1 : Operator BotAB .bot) ce38U j false = ⊤ := by
    intro j
    unfold zeroingMatrix uniformZeroRadiusComp uniformZeroRadius uniformZeroRadiusOn
    apply le_antisymm le_top
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    rw [pointwiseZeroRadius_eq_top_of_forall_pos _ _ _ _ _ (hadm_all j y hy)]
  refine ⟨ce38Dist_is_extended, hU_ne, hU_dom, ⟨hmat_top false, ?_⟩, ⟨hmat_top true, ?_⟩⟩
  · intro h
    have h0 := h .a (Or.inl rfl) .b (Or.inr rfl)
    simp [ce38Dist] at h0
  · intro h
    have h0 := h .a (Or.inl rfl) .b (Or.inr rfl)
    simp [ce38Dist] at h0

end Counterexamples33

end Ch03

