import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.ENNReal.Operations
import Mathlib.Data.Matrix.Mul

/-!
# 分量通道与矩阵界

本文件将 Zhe Li（Glen Li / glenzli）《The Operator Evolution Theory》
卷一 §2.1、§2.2 和习题 2.2 的指定选段改写为 Lean 证明。
原著 https://glenzli.com/books/oet/ ，DOI 10.5281/zenodo.21457931 ，
ORCID 0009-0006-6536-3453 ，许可 https://creativecommons.org/licenses/by/4.0/ 。
-/

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

namespace LCH01

noncomputable section

variable {X I : Type} {bot : X}

abbrev CoeffMatrix (I : Type) := Matrix I I ENNReal

/-- 通道按输入、输出命名，矩阵按行、列存取。 -/
def entry (M : CoeffMatrix I) (i j : I) : ENNReal := M j i

theorem entry_mul [Fintype I] (B A : CoeffMatrix I) (i j : I) :
    entry (B * A) i j = ∑ k, entry B k j * entry A i k :=
  Matrix.mul_apply

def rowValue [Fintype I] (M : CoeffMatrix I) (v : I → ENNReal) (j : I) : ENNReal :=
  ∑ k, entry M k j * v k

/-- 正文的有限非空规范族，每个分量使用冻结模块的扩展伪度量。 -/
structure Gauge (X I : Type) (bot : X) [Fintype I] [Nonempty I] where
  dist : I → X → X → ENNReal
  metric : ∀ i, ExtendedPseudoMetric X bot (dist i)

variable [Fintype I] [Nonempty I]

def IsLipOn (G : Gauge X I bot) (φ : Operator X bot) (U : Set X)
    (L : CoeffMatrix I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    G.dist j (φ.func x) (φ.func y) ≤ rowValue L (fun i => G.dist i x y) j

def IsLip (G : Gauge X I bot) (φ : Operator X bot) (L : CoeffMatrix I) : Prop :=
  IsLipOn G φ (dom φ) L

def lipFamilyOn (G : Gauge X I bot) (φ : Operator X bot) (U : Set X) :
    Set (CoeffMatrix I) := {L | IsLipOn G φ U L}

def lipFamily (G : Gauge X I bot) (φ : Operator X bot) : Set (CoeffMatrix I) :=
  {L | IsLip G φ L}

def IsCoLipOn (G : Gauge X I bot) (φ : Operator X bot) (U : Set X)
    (K : CoeffMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    rowValue K (fun i => G.dist i x y) j ≤ G.dist j (φ.func x) (φ.func y)

def coLipFamilyOn (G : Gauge X I bot) (φ : Operator X bot) (U : Set X) :
    Set (CoeffMatrix I) := {K | IsCoLipOn G φ U K}

variable {G : Gauge X I bot} {φ : Operator X bot} {U : Set X}
variable {L K : CoeffMatrix I} {x y : X} {i j : I}

theorem coLip_term_le (hK : K ∈ coLipFamilyOn G φ U) (i j : I)
    (hx : x ∈ U) (hy : y ∈ U) :
    entry K i j * G.dist i x y ≤ G.dist j (φ.func x) (φ.func y) := by
  have hsum : entry K i j * G.dist i x y ≤ rowValue K (fun k => G.dist k x y) j :=
    Finset.single_le_sum (fun k _ => zero_le (entry K k j * G.dist k x y))
      (Finset.mem_univ i)
  exact hsum.trans (hK.2.2 x hx y hy j)

abbrev Channel (I : Type) := I × I

def OnlyInput (M : CoeffMatrix I) (c : Channel I) : Prop :=
  ∀ k, k ≠ c.1 → entry M k c.2 = 0

def IsDiagonal (M : CoeffMatrix I) : Prop := ∀ j, OnlyInput M (j, j)

omit [Fintype I] [Nonempty I] in
theorem zero_channel_term (M : CoeffMatrix I) (c : Channel I) (v : I → ENNReal)
    (h : entry M c.1 c.2 = 0) : entry M c.1 c.2 * v c.1 = 0 := by
  rw [h, zero_mul]

omit [Nonempty I] in
theorem rowValue_onlyInput {M : CoeffMatrix I} {i j : I} (h : OnlyInput M (i, j))
    (v : I → ENNReal) : rowValue M v j = entry M i j * v i := by
  classical
  unfold rowValue
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [h k hki, zero_mul]
  · simp

theorem lip_onlyInput (hL : L ∈ lipFamilyOn G φ U) (h : OnlyInput L (i, j))
    (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ entry L i j * G.dist i x y :=
  (hL.2 x hx y hy j).trans_eq (rowValue_onlyInput h _)

theorem lip_diagonal (hL : L ∈ lipFamilyOn G φ U) (h : IsDiagonal L)
    (j : I) (hx : x ∈ U) (hy : y ∈ U) :
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  lip_onlyInput hL (h j) hx hy

theorem positive_channel (hK : K ∈ coLipFamilyOn G φ U) (hc : 0 < entry K i j)
    (hx : x ∈ U) (hy : y ∈ U) (hd : 0 < G.dist i x y) :
    0 < G.dist j (φ.func x) (φ.func y) :=
  (ENNReal.mul_pos_iff.mpr ⟨hc, hd⟩).trans_le (coLip_term_le hK i j hx hy)

theorem reflects_gauge_zero (hK : K ∈ coLipFamilyOn G φ U)
    (hdiag : ∀ j, 0 < entry K j j) (hx : x ∈ U) (hy : y ∈ U)
    (hzero : GaugeZeroRelated G.dist (φ.func x) (φ.func y)) :
    GaugeZeroRelated G.dist x y := by
  intro j
  by_contra hn
  have hout := positive_channel hK (hdiag j) hx hy (pos_iff_ne_zero.mpr hn)
  exact (ne_of_gt hout) (hzero j)

theorem diagonal_two_sided (hL : L ∈ lipFamilyOn G φ U) (hK : K ∈ coLipFamilyOn G φ U)
    (h : OnlyInput L (j, j)) (hx : x ∈ U) (hy : y ∈ U) :
    entry K j j * G.dist j x y ≤ G.dist j (φ.func x) (φ.func y) ∧
    G.dist j (φ.func x) (φ.func y) ≤ entry L j j * G.dist j x y :=
  ⟨coLip_term_le hK j j hx hy, lip_onlyInput hL h hx hy⟩

end

end LCH01
