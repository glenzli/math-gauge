import LCH01.MatrixBounds

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations

set_option linter.style.longLine false

/-!
# 第 2 章 算子界 · 分量通道接口与习题 2.2

形式化覆盖义务：
- `CH02-D07`：分量通道 $(i, j)$、单输入通道/单行稀疏条件与对角矩阵特例。
- `CH02-P19`：单一输入项行化简及对角矩阵同分量通道特例。
- `CH02-P20`：命题 2.8 (i) 正 co-Lip 通道保持正距离。
- `CH02-P21`：命题 2.8 (ii) 全对角正 co-Lip 反射族零距关系（保持 $\sim_{\mathcal{G}}$，不加强为点相等）。
- `CH02-P25`：习题 2.2 对角输入项的标量双侧界。
-/

/--
OET §2.2（`CH02-D07`）：从输入分量 $d_i$ 到输出分量 $d_j$ 的分量通道有序对 $(i, j)$。
-/
abbrev ComponentChannel (I : Type) : Type := I × I

/--
OET §2.2（`CH02-D07`）：同分量（对角）通道 $(i, i)$。
-/
def diagChannel {I : Type} (i : I) : ComponentChannel I := (i, i)

/--
OET §2.2（`CH02-D07`）：矩阵 `M` 在分量通道 `c = (i, j)` 上的系数 $M_{i \to j}$。
-/
def channelCoeff {I : Type} (M : GaugeMatrix I) (c : ComponentChannel I) : ENNReal :=
  channelEntry M c.1 c.2

/--
OET §2.2（`CH02-D07`）：单行稀疏（单输入通道）条件——第 `j` 行除输入通道 `(i, j)` 的条目 $M_{i \to j}$ 外均为零，
即 $\forall k \neq i,\; M_{k \to j} = 0$。
-/
def IsSingleInputRow {I : Type} (M : GaugeMatrix I) (i j : I) : Prop :=
  ∀ k : I, k ≠ i → channelEntry M k j = 0

/--
OET §2.2 & 习题 2.2（`CH02-D07`）：第 `j` 行只保留对角输入项 `(j, j)` 的稀疏条件，
即 $\forall k \neq j,\; M_{k \to j} = 0$。
-/
abbrev IsDiagonalRow {I : Type} (M : GaugeMatrix I) (j : I) : Prop :=
  IsSingleInputRow M j j

/--
OET §2.2（`CH02-D07`）：对角矩阵特例——所有跨分量通道条目均为零，
即 $\forall i, j \in I,\; i \neq j \Rightarrow M_{i \to j} = 0$。
-/
def IsDiagonalGaugeMatrix {I : Type} (M : GaugeMatrix I) : Prop :=
  ∀ i j : I, i ≠ j → channelEntry M i j = 0

/-- 对角规范矩阵谓词等价于行列表示下所有非对角元为零（$\forall j \neq i,\; (\mathbf{M})_{ji} = 0$）。 -/
theorem isDiagonalGaugeMatrix_iff_offDiag_zero {I : Type} (M : GaugeMatrix I) :
    IsDiagonalGaugeMatrix M ↔ ∀ j i : I, j ≠ i → M j i = 0 := by
  constructor
  · intro h j i hji
    exact h i j hji.symm
  · intro h i j hij
    exact h j i hij.symm

/-- 矩阵为对角矩阵当且仅当每一输出行都只保留同分量对角输入项。 -/
theorem isDiagonalGaugeMatrix_iff_forall_diagonalRow {I : Type} (M : GaugeMatrix I) :
    IsDiagonalGaugeMatrix M ↔ ∀ j : I, IsDiagonalRow M j := by
  constructor
  · intro h j k hkj
    exact h k j hkj
  · intro h i j hij
    exact h j i hij

/--
OET §2.2（`CH02-P19`）：当第 `j` 行除 $L_{i \to j}$ 外均为零时，行加权距离和化简为单一输入项
$\sum_{k \in I} L_{k \to j} d_k(x, y) = L_{i \to j} d_i(x, y)$。
-/
theorem single_input_row_sum_eq {X I : Type} [Fintype I]
    (d : I → X → X → ENNReal) (L : GaugeMatrix I) (i j : I)
    (hrow : IsSingleInputRow L i j) (x y : X) :
    (∑ k : I, channelEntry L k j * d k x y) = channelEntry L i j * d i x y := by
  refine Finset.sum_eq_single i ?_ ?_
  · intro k _ hki
    rw [hrow k hki, zero_mul]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

/--
OET §2.2（`CH02-P19`）：单一输入项行化简。
设 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$（含 $U \subseteq \mathrm{dom}(\phi)$），且第 `j` 行除 $L_{i \to j}$ 外均为零，
则对任意 $x, y \in U$，有
$\sum_{k \in I} L_{k \to j} d_k(x, y) = L_{i \to j} d_i(x, y)$ 且
$d_j(\phi(x), \phi(y)) \le L_{i \to j} d_i(x, y)$。
-/
theorem restricted_lip_single_input_row {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (hL : L ∈ restrictedLipFamily d ϕ U) (i j : I)
    (hrow : IsSingleInputRow L i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      (∑ k : I, channelEntry L k j * d k x y) = channelEntry L i j * d i x y ∧
        d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L i j * d i x y := by
  intro x hx y hy
  have hsum : (∑ k : I, channelEntry L k j * d k x y) = channelEntry L i j * d i x y :=
    single_input_row_sum_eq d L i j hrow x y
  refine ⟨hsum, ?_⟩
  calc
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, channelEntry L k j * d k x y := hL.2 x hx y hy j
    _ = channelEntry L i j * d i x y := hsum

/--
OET §2.2（`CH02-P19` 对角特例）：若 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 为对角矩阵，
则对每个同分量通道 $(i, i)$ 及任意 $x, y \in U$，均有单输入项行化简与标量上界
$d_i(\phi(x), \phi(y)) \le L_{i \to i} d_i(x, y)$。
-/
theorem restricted_lip_diagonal {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I)
    (hL : L ∈ restrictedLipFamily d ϕ U)
    (hdiag : IsDiagonalGaugeMatrix L) :
    ∀ i : I, ∀ x ∈ U, ∀ y ∈ U,
      (∑ k : I, channelEntry L k i * d k x y) = channelEntry L i i * d i x y ∧
        d i (ϕ.func x) (ϕ.func y) ≤ channelEntry L i i * d i x y := by
  intro i x hx y hy
  have hrow : IsSingleInputRow L i i :=
    (isDiagonalGaugeMatrix_iff_forall_diagonalRow L).mp hdiag i
  exact restricted_lip_single_input_row d ϕ U L hL i i hrow x hx y hy

/--
辅助引理：受限 co-Lip 证书给出任一单通道下界
$K_{i \to j} d_i(x, y) \le d_j(\phi(x), \phi(y))$（$x, y \in U$）。
-/
theorem restricted_colip_channel_le {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (hK : K ∈ restrictedCoLipFamily d ϕ U) (i j : I) :
    ∀ x ∈ U, ∀ y ∈ U,
      channelEntry K i j * d i x y ≤ d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy
  calc
    channelEntry K i j * d i x y
        ≤ ∑ k : I, channelEntry K k j * d k x y := by
          exact Finset.single_le_sum
            (f := fun k => channelEntry K k j * d k x y)
            (fun k _ => zero_le (channelEntry K k j * d k x y))
            (Finset.mem_univ i)
    _ ≤ d j (ϕ.func x) (ϕ.func y) := hK.2.2 x hx y hy j

/--
OET 命题 2.8 (i)（`CH02-P20`）：正 co-Lip 通道保持正距离（可分辨性）。
设 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$ 且 $K_{i \to j} > 0$，则对任意 $x, y \in U$，
$d_i(x, y) > 0 \Rightarrow d_j(\phi(x), \phi(y)) > 0$。
-/
theorem restricted_colip_pos_channel {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (hK : K ∈ restrictedCoLipFamily d ϕ U) {i j : I}
    (hpos : 0 < channelEntry K i j) :
    ∀ x ∈ U, ∀ y ∈ U,
      0 < d i x y → 0 < d j (ϕ.func x) (ϕ.func y) := by
  intro x hx y hy hdi
  have hmul_pos : 0 < channelEntry K i j * d i x y :=
    ENNReal.mul_pos (pos_iff_ne_zero.mp hpos) (pos_iff_ne_zero.mp hdi)
  exact lt_of_lt_of_le hmul_pos (restricted_colip_channel_le d ϕ U K hK i j x hx y hy)

/--
OET 命题 2.8 (ii)（`CH02-P21`）：全对角正 co-Lip 反射族零距关系。
设 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$ 且对所有 $j \in I$ 有 $K_{j \to j} > 0$，
则对任意 $x, y \in U$，$\phi(x) \sim_{\mathcal{G}} \phi(y) \Rightarrow x \sim_{\mathcal{G}} y$
（结论严格保持 `GaugeZeroRelated`，不预设族分离性、不加强为 $x = y$）。
-/
theorem restricted_colip_reflects_gauge_zero {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I)
    (hK : K ∈ restrictedCoLipFamily d ϕ U)
    (hdiag_pos : ∀ j : I, 0 < channelEntry K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated d (ϕ.func x) (ϕ.func y) → GaugeZeroRelated d x y := by
  intro x hx y hy hzero j
  by_contra hdj_ne
  have hdj_pos : 0 < d j x y := pos_iff_ne_zero.mpr hdj_ne
  have hphi_pos : 0 < d j (ϕ.func x) (ϕ.func y) :=
    restricted_colip_pos_channel d ϕ U K hK (hdiag_pos j) x hx y hy hdj_pos
  exact (ne_of_gt hphi_pos) (hzero j)

/--
OET 习题 2.2（`CH02-P25`）：对角输入项的标量双侧界。
设 $\phi \in \mathcal{X}_{\mathrm{op}}$，$U \subseteq \mathrm{dom}(\phi)$，$j \in I$，
给定 $\mathbf{L} \in \mathscr{L}(\phi)\big|_U$ 与 $\mathbf{K} \in \mathscr{K}(\phi)\big|_U$。
若第 $j$ 行满足 $\forall k \neq j,\; L_{k \to j} = 0$（即 `IsDiagonalRow L j`），
则对任意 $x, y \in U$ 有
$K_{j \to j} \cdot d_j(x, y) \le d_j(\phi(x), \phi(y)) \le L_{j \to j} \cdot d_j(x, y)$。
-/
theorem scalar_two_sided_bound_of_diagonal_row {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (j : I)
    (L K : GaugeMatrix I)
    (hL : L ∈ restrictedLipFamily d ϕ U)
    (hK : K ∈ restrictedCoLipFamily d ϕ U)
    (hL_row : IsDiagonalRow L j) :
    ∀ x ∈ U, ∀ y ∈ U,
      channelEntry K j j * d j x y ≤ d j (ϕ.func x) (ϕ.func y) ∧
        d j (ϕ.func x) (ϕ.func y) ≤ channelEntry L j j * d j x y := by
  intro x hx y hy
  refine ⟨restricted_colip_channel_le d ϕ U K hK j j x hx y hy, ?_⟩
  exact (restricted_lip_single_input_row d ϕ U L hL j j hL_row x hx y hy).2
