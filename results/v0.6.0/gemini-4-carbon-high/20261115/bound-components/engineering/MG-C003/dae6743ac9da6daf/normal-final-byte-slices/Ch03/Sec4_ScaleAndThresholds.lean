import Ch03.Defs
import Ch03.RealLineExt

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open Set

/-!
# § 3.4 输入尺度与零化阈值 (`CH03-P16-01` – `CH03-P17-04`)
-/

/-! ## 引理 3.13：两项阈值分类及其单调性 (`CH03-P16-01` – `CH03-P16-03`) -/

/-- 四类阈值组合对应的通道集合（按底层不等式直接刻画）。 -/
def channelRegime11 {X I : Type} {bot : X}
    (σ : I → Set X → ENNReal) (τ_σ τ_N : ENNReal)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X) : Set (I × I) :=
  { p | σ p.1 A < τ_σ ∧ τ_N ≤ uniformNullRadiusComp d f p.1 p.2 A }

def channelRegime10 {X I : Type} {bot : X}
    (σ : I → Set X → ENNReal) (τ_σ τ_N : ENNReal)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X) : Set (I × I) :=
  { p | σ p.1 A < τ_σ ∧ uniformNullRadiusComp d f p.1 p.2 A < τ_N }

def channelRegime01 {X I : Type} {bot : X}
    (σ : I → Set X → ENNReal) (τ_σ τ_N : ENNReal)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X) : Set (I × I) :=
  { p | τ_σ ≤ σ p.1 A ∧ τ_N ≤ uniformNullRadiusComp d f p.1 p.2 A }

def channelRegime00 {X I : Type} {bot : X}
    (σ : I → Set X → ENNReal) (τ_σ τ_N : ENNReal)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X) : Set (I × I) :=
  { p | τ_σ ≤ σ p.1 A ∧ uniformNullRadiusComp d f p.1 p.2 A < τ_N }

/-- `CH03-P16-01`：引理 3.13（四种阈值组合互斥且穷尽）— 每个通道 `(i, j)` 唯一落入四种不等式组合之一，并与 `Type_{f, A}(i, j) ∈ {(1,1), (1,0), (0,1), (0,0)}` 一一对应。 -/
theorem lemma_3_13_threshold_partition {X I : Type} {bot : X}
    (σ : I → Set X → ENNReal) (τ_σ τ_N : ENNReal)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X)
    (hσ_fam : IsInputScaleFamily σ)
    (hτ_σ : IsFinitePosThreshold τ_σ) (hτ_N : IsFinitePosThreshold τ_N)
    (hA_ne : A.Nonempty) (hA_dom : A ⊆ dom f) :
    (∀ i j : I,
      (channelType σ τ_σ τ_N d f A i j = (1, 1) ↔ (i, j) ∈ channelRegime11 σ τ_σ τ_N d f A) ∧
      (channelType σ τ_σ τ_N d f A i j = (1, 0) ↔ (i, j) ∈ channelRegime10 σ τ_σ τ_N d f A) ∧
      (channelType σ τ_σ τ_N d f A i j = (0, 1) ↔ (i, j) ∈ channelRegime01 σ τ_σ τ_N d f A) ∧
      (channelType σ τ_σ τ_N d f A i j = (0, 0) ↔ (i, j) ∈ channelRegime00 σ τ_σ τ_N d f A)) ∧
    Disjoint (channelRegime11 σ τ_σ τ_N d f A) (channelRegime10 σ τ_σ τ_N d f A) ∧
    Disjoint (channelRegime11 σ τ_σ τ_N d f A) (channelRegime01 σ τ_σ τ_N d f A) ∧
    Disjoint (channelRegime11 σ τ_σ τ_N d f A) (channelRegime00 σ τ_σ τ_N d f A) ∧
    Disjoint (channelRegime10 σ τ_σ τ_N d f A) (channelRegime01 σ τ_σ τ_N d f A) ∧
    Disjoint (channelRegime10 σ τ_σ τ_N d f A) (channelRegime00 σ τ_σ τ_N d f A) ∧
    Disjoint (channelRegime01 σ τ_σ τ_N d f A) (channelRegime00 σ τ_σ τ_N d f A) ∧
    (channelRegime11 σ τ_σ τ_N d f A ∪ channelRegime10 σ τ_σ τ_N d f A ∪
      channelRegime01 σ τ_σ τ_N d f A ∪ channelRegime00 σ τ_σ τ_N d f A = Set.univ) := by
  classical
  have _ := hσ_fam
  have _ := hτ_σ
  have _ := hτ_N
  have _ := hA_ne
  have _ := hA_dom
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases h1 : σ i A < τ_σ <;> by_cases h2 : τ_N ≤ uniformNullRadiusComp d f i j A <;>
      simp [channelType, ind01, channelRegime11, channelRegime10, channelRegime01,
        channelRegime00, h1, h2, not_lt.mp, not_le.mp]
  · exact Set.disjoint_left.mpr (fun _ h₁ h₂ => (not_lt_of_ge h₁.2) h₂.2)
  · exact Set.disjoint_left.mpr (fun _ h₁ h₂ => (not_lt_of_ge h₂.1) h₁.1)
  · exact Set.disjoint_left.mpr (fun _ h₁ h₂ => (not_lt_of_ge h₂.1) h₁.1)
  · exact Set.disjoint_left.mpr (fun _ h₁ h₂ => (not_lt_of_ge h₂.1) h₁.1)
  · exact Set.disjoint_left.mpr (fun _ h₁ h₂ => (not_lt_of_ge h₂.1) h₁.1)
  · exact Set.disjoint_left.mpr (fun _ h₁ h₂ => (not_lt_of_ge h₁.2) h₂.2)
  · ext ⟨i, j⟩
    simp only [Set.mem_union, Set.mem_univ, iff_true,
      channelRegime11, channelRegime10, channelRegime01, channelRegime00, Set.mem_setOf_eq]
    rcases lt_or_ge (σ i A) τ_σ with h1 | h1 <;>
      rcases le_or_gt τ_N (uniformNullRadiusComp d f i j A) with h2 | h2
    · exact Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨h1, h2⟩))
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inr ⟨h1, h2⟩

/-- `CH03-P16-02`：引理 3.13(i) — 固定其他数据，当输入尺度阈值 `τ_σ` 增大时，第一项取 `1` 的通道集合单调不减。 -/
theorem lemma_3_13_first_mono_in_tau_sigma {X I : Type} {bot : X}
    (σ : I → Set X → ENNReal) (τ_σ τ'_σ τ_N : ENNReal)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X)
    (hτ : τ_σ ≤ τ'_σ) :
    { p : I × I | (channelType σ τ_σ τ_N d f A p.1 p.2).1 = 1 } ⊆
      { p : I × I | (channelType σ τ'_σ τ_N d f A p.1 p.2).1 = 1 } := by
  classical
  rintro ⟨i, j⟩ hp
  simp only [Set.mem_setOf_eq, channelType, ind01] at hp ⊢
  split_ifs at hp with hlt
  rw [if_pos (lt_of_lt_of_le hlt hτ)]

/-- `CH03-P16-03`：引理 3.13(ii) — 固定其他数据，当零化阈值 `τ_N` 增大时，第二项取 `1` 的通道集合单调不增。 -/
theorem lemma_3_13_second_antitone_in_tau_N {X I : Type} {bot : X}
    (σ : I → Set X → ENNReal) (τ_σ τ_N τ'_N : ENNReal)
    (d : I → X → X → ENNReal) (f : Operator X bot) (A : Set X)
    (hτ : τ_N ≤ τ'_N) :
    { p : I × I | (channelType σ τ_σ τ'_N d f A p.1 p.2).2 = 1 } ⊆
      { p : I × I | (channelType σ τ_σ τ_N d f A p.1 p.2).2 = 1 } := by
  classical
  rintro ⟨i, j⟩ hp
  simp only [Set.mem_setOf_eq, channelType, ind01] at hp ⊢
  split_ifs at hp with hge
  rw [if_pos (le_trans hτ hge)]

/-! ## 命题 3.14：域缩小下的尺度与统一零化半径单调性 (`CH03-P17-01` – `CH03-P17-04`) -/

/-- `CH03-P17-01`：命题 3.14(i) — 对任意输入尺度函数族与 `∅ ≠ B ⊆ A ⊆ dom(f)`，有 `σ_i(B) ≤ σ_i(A)`，且 `σ_i(A) < τ_σ ⟹ σ_i(B) < τ_σ`。 -/
theorem prop_3_14_scale_mono_on_shrink {X I : Type} {bot : X}
    (σ : I → Set X → ENNReal) (f : Operator X bot) (A B : Set X)
    (i : I) (τ_σ : ENNReal)
    (hσ : IsInputScaleFamily σ)
    (hB_ne : B.Nonempty) (hBA : B ⊆ A) (hA_dom : A ⊆ dom f) :
    σ i B ≤ σ i A ∧ (σ i A < τ_σ → σ i B < τ_σ) := by
  have _ := hA_dom
  have hA_ne : A.Nonempty := hB_ne.mono hBA
  have hle : σ i B ≤ σ i A := hσ i hB_ne hA_ne hBA
  exact ⟨hle, fun hlt => lt_of_le_of_lt hle hlt⟩

/-- `CH03-P17-02`：命题 3.14(ii-a) — 固定基点 `x ∈ B` 且 `B ⊆ A ⊆ dom(f)` 时，缩小评估域使点态零化半径单调不减：`r^N_{f, i, j}(x | B) ≥ r^N_{f, i, j}(x | A)`。 -/
theorem prop_3_14_pointwise_nullRadius_antitone {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot) (A B : Set X)
    (i j : I) (x : X)
    (hx : x ∈ B) (hBA : B ⊆ A) (hA_dom : A ⊆ dom f) :
    nullRadiusComp d f i j x A ≤ nullRadiusComp d f i j x B := by
  have _ := hx
  have _ := hA_dom
  apply sSup_le
  rintro r ⟨hr_pos, hr_fin, hincA⟩
  apply le_sSup
  refine ⟨hr_pos, hr_fin, ?_⟩
  intro z ⟨hz_ball, hzB⟩
  have hzA := hincA ⟨hz_ball, hBA hzB⟩
  exact ⟨hzB, hzA.2⟩

/-- `CH03-P17-03`：命题 3.14(ii-b) — 当 `∅ ≠ B ⊆ A ⊆ dom(f)` 时，同时缩小评估域与取下确界的基点集合，统一零化半径单调不减（含正文两步不等式链）。 -/
theorem prop_3_14_uniform_nullRadius_antitone {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot) (A B : Set X)
    (i j : I)
    (hB_ne : B.Nonempty) (hBA : B ⊆ A) (hA_dom : A ⊆ dom f) :
    uniformNullRadiusComp d f i j A ≤ uniformNullRadiusCompOn d f i j B A ∧
    uniformNullRadiusCompOn d f i j B A ≤ uniformNullRadiusComp d f i j B ∧
    uniformNullRadiusComp d f i j A ≤ uniformNullRadiusComp d f i j B := by
  have _ := hB_ne
  have hstep1 : uniformNullRadiusComp d f i j A ≤ uniformNullRadiusCompOn d f i j B A := by
    unfold uniformNullRadiusComp uniformNullRadius uniformNullRadiusCompOn uniformNullRadiusOn
    apply le_iInf₂
    intro x hxB
    exact iInf₂_le x (hBA hxB)
  have hstep2 : uniformNullRadiusCompOn d f i j B A ≤ uniformNullRadiusComp d f i j B := by
    unfold uniformNullRadiusComp uniformNullRadius uniformNullRadiusCompOn uniformNullRadiusOn
    apply le_iInf₂
    intro x hxB
    exact le_trans (iInf₂_le x hxB)
      (prop_3_14_pointwise_nullRadius_antitone d f A B i j x hxB hBA hA_dom)
  exact ⟨hstep1, hstep2, le_trans hstep1 hstep2⟩

/-- 命题 3.14(iii) 反例集合 `A = {0, 1}` 与 `B = {0}`。 -/
def shrinkScaleSetA : Set RealWithBot := {.ofReal 0, .ofReal 1}
def shrinkScaleSetB : Set RealWithBot := {.ofReal 0}

/-- `RealWithBot` 上的恒等算子显式缩写。 -/
def realIdOp : Operator RealWithBot RealWithBot.bot := operator_identity

/-- `CH03-P17-04`：命题 3.14(iii) — 带吸收元实线上的二点/单点直径尺度反例：
`∅ ≠ B ⊆ A ⊆ dom(id)`，`diam(B) = 0 < 1/2` 而 `diam(A) = 1 ≥ 1/2`，故反向尺度判断不成立。 -/
theorem prop_3_14_reverse_scale_counterexample :
    shrinkScaleSetB.Nonempty ∧
    shrinkScaleSetB ⊆ shrinkScaleSetA ∧
    shrinkScaleSetA ⊆ dom realIdOp ∧
    setDiam realStdExtDist shrinkScaleSetB = 0 ∧
    setDiam realStdExtDist shrinkScaleSetA = 1 ∧
    setDiam realStdExtDist shrinkScaleSetB < (1 / 2 : ENNReal) ∧
    (1 / 2 : ENNReal) ≤ setDiam realStdExtDist shrinkScaleSetA ∧
    ¬ (setDiam realStdExtDist shrinkScaleSetB < (1 / 2 : ENNReal) →
        setDiam realStdExtDist shrinkScaleSetA < (1 / 2 : ENNReal)) := by
  have hB_ne : shrinkScaleSetB.Nonempty := ⟨.ofReal 0, Set.mem_singleton _⟩
  have hBA : shrinkScaleSetB ⊆ shrinkScaleSetA := by
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact Or.inl rfl
  have hA_dom : shrinkScaleSetA ⊆ dom realIdOp := by
    intro x hx
    rcases hx with rfl | rfl <;> simp [dom, realIdOp, operator_identity]
  have hdiamB : setDiam realStdExtDist shrinkScaleSetB = 0 := by
    apply le_antisymm _ (zero_le _)
    unfold setDiam
    apply iSup₂_le
    intro x hx
    apply iSup₂_le
    intro y hy
    rw [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]
    simp
  have hdiamA : setDiam realStdExtDist shrinkScaleSetA = 1 := by
    apply le_antisymm
    · unfold setDiam
      apply iSup₂_le
      intro x hx
      apply iSup₂_le
      intro y hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp
    · unfold setDiam
      have h0 : RealWithBot.ofReal 0 ∈ shrinkScaleSetA := Or.inl rfl
      have h1 : RealWithBot.ofReal 1 ∈ shrinkScaleSetA := Or.inr rfl
      refine le_trans ?_
        (le_iSup₂_of_le (RealWithBot.ofReal 0) h0
          (le_iSup₂_of_le (RealWithBot.ofReal 1) h1 le_rfl))
      simp
  have hB_lt : setDiam realStdExtDist shrinkScaleSetB < (1 / 2 : ENNReal) := by
    rw [hdiamB]
    exact ENNReal.div_pos one_ne_zero (by simp)
  have hA_ge : (1 / 2 : ENNReal) ≤ setDiam realStdExtDist shrinkScaleSetA := by
    rw [hdiamA]
    exact ENNReal.half_le_self
  refine ⟨hB_ne, hBA, hA_dom, hdiamB, hdiamA, hB_lt, hA_ge, ?_⟩
  intro himp
  exact (not_lt_of_ge hA_ge) (himp hB_lt)

end Ch03
