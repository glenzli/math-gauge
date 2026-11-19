import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Operations
import Mathlib.LinearAlgebra.Matrix.IsDiag

/-!
本文件形式化 Zhe Li（Glen Li / glenzli）《The Operator Evolution Theory》
第一卷 v1.0.0 的 §2.1、§2.2 与习题 2.2 选段。
[原作](https://glenzli.com/books/oet/) · [DOI](https://doi.org/10.5281/zenodo.21457931) ·
[原作仓库](https://gitlab.com/glenzli/oet-public) ·
[ORCID](https://orcid.org/0009-0006-6536-3453) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)
-/

namespace LCH01

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

noncomputable section

/-- 第一章的有限非空规范族，每个分量采用冻结模块的扩展伪度量。 -/
structure Gauge (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ENNReal
  component : ∀ i, ExtendedPseudoMetric X bot (dist i)

variable {X I : Type} {bot : X}

/-! ### §2.1 矩阵约定与证书族 -/

/-- 输入 i 对应列，输出 j 对应行。 -/
abbrev BoundMatrix (I : Type) := Matrix I I ENNReal

def entry (M : BoundMatrix I) (i j : I) : ENNReal := M j i

theorem entry_mul [Fintype I] (B A : BoundMatrix I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k :=
  Matrix.mul_apply

section Certificates

variable [Fintype I] [Nonempty I] (G : Gauge X I bot) (φ : Operator X bot)

def rowSum (M : BoundMatrix I) (j : I) (x y : X) : ENNReal :=
  ∑ i, entry M i j * G.dist i x y

def IsLipOn (U : Set X) (L : BoundMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    G.dist j (φ.func x) (φ.func y) ≤ rowSum G L j x y

def IsLip (L : BoundMatrix I) : Prop := IsLipOn G φ (dom φ) L

def lipMatricesOn (U : Set X) : Set (BoundMatrix I) := {L | IsLipOn G φ U L}

def lipMatrices : Set (BoundMatrix I) := {L | IsLip G φ L}

def IsCoLipOn (U : Set X) (K : BoundMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    rowSum G K j x y ≤ G.dist j (φ.func x) (φ.func y)

def coLipMatricesOn (U : Set X) : Set (BoundMatrix I) := {K | IsCoLipOn G φ U K}

end Certificates

/-! ### §2.2 分量通道 -/

/-- (i, j) 表示从输入分量 i 到输出分量 j 的通道。 -/
abbrev Channel (I : Type) := I × I

def OnlyInput (M : BoundMatrix I) (c : Channel I) : Prop :=
  ∀ k, k ≠ c.1 → entry M k c.2 = 0

theorem channel_term_zero {M : BoundMatrix I} (c : Channel I)
    (h : entry M c.1 c.2 = 0) (r : ENNReal) : entry M c.1 c.2 * r = 0 := by
  rw [h, zero_mul]

theorem isDiag_iff_onlyInput (M : BoundMatrix I) :
    M.IsDiag ↔ ∀ j, OnlyInput M (j, j) := by
  constructor
  · intro h j k hk
    exact h (Ne.symm hk)
  · intro h j k hjk
    exact h j k (Ne.symm hjk)

variable [Fintype I] [Nonempty I] {G : Gauge X I bot} {φ : Operator X bot}
variable {U : Set X} {L K : BoundMatrix I} {x y : X} {i j : I}

theorem rowSum_single (M : BoundMatrix I) (hrow : OnlyInput M (i, j)) (x y : X) :
    rowSum G M j x y = entry M i j * G.dist i x y := by
  unfold rowSum
  apply Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
  intro k _ hk
  exact channel_term_zero (k, j) (hrow k hk) (G.dist k x y)

theorem lip_single_input (hL : L ∈ lipMatricesOn G φ U) (hrow : OnlyInput L (i, j))
    (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ entry L i j * G.dist i x y := by
  calc
    _ ≤ rowSum G L j x y := hL.2 x hx y hy j
    _ = _ := rowSum_single L hrow x y

theorem lip_diagonal (hL : L ∈ lipMatricesOn G φ U) (hd : L.IsDiag) (j : I)
    (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  lip_single_input hL ((isDiag_iff_onlyInput L).mp hd j) hx hy

/-- co-Lip 行和控制该行中的每个非负项。 -/
theorem coLip_term_le (hK : K ∈ coLipMatricesOn G φ U) (i j : I)
    (hx : x ∈ U) (hy : y ∈ U) :
    entry K i j * G.dist i x y ≤ G.dist j (φ.func x) (φ.func y) := by
  calc
    _ ≤ rowSum G K j x y :=
      Finset.single_le_sum (fun k _ => zero_le (entry K k j * G.dist k x y))
        (Finset.mem_univ i)
    _ ≤ _ := hK.2.2 x hx y hy j

/-- 命题 2.8(i)。 -/
theorem positive_channel (hK : K ∈ coLipMatricesOn G φ U) (hc : 0 < entry K i j)
    (hx : x ∈ U) (hy : y ∈ U) (hin : 0 < G.dist i x y) :
    0 < G.dist j (φ.func x) (φ.func y) :=
  lt_of_lt_of_le (ENNReal.mul_pos_iff.mpr ⟨hc, hin⟩) (coLip_term_le hK i j hx hy)

/-- 命题 2.8(ii)。 -/
theorem reflects_gauge_zero (hK : K ∈ coLipMatricesOn G φ U)
    (hd : ∀ j, 0 < entry K j j) (hx : x ∈ U) (hy : y ∈ U)
    (hout : GaugeZeroRelated G.dist (φ.func x) (φ.func y)) :
    GaugeZeroRelated G.dist x y := by
  intro j
  by_contra hn
  exact (positive_channel hK (hd j) hx hy (pos_iff_ne_zero.mpr hn)).ne' (hout j)

/-- 习题 2.2，对角输入项的标量双侧界。 -/
theorem scalar_two_sided (hL : L ∈ lipMatricesOn G φ U) (hK : K ∈ coLipMatricesOn G φ U)
    (hrow : OnlyInput L (j, j)) (hx : x ∈ U) (hy : y ∈ U) :
    entry K j j * G.dist j x y ≤ G.dist j (φ.func x) (φ.func y) ∧
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  ⟨coLip_term_le hK j j hx hy, lip_single_input hL hrow hx hy⟩

end

end LCH01
