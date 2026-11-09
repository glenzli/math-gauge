import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# 第 2 章 算子界（h-5d30f7f93769bbd7）的形式化

约定与表示：
* 语境 `G : GaugeSpace X bot I`：`I` 为有限非空类型（`[Fintype I] [Nonempty I]`），
  `G.d i` 为第 1 章意义下的扩展伪度量（`ExtendedPseudoMetric`，含吸收元隔离）；
  算子为第 1 章的 `Operator X bot`（保持吸收元），定义域为 `dom`，像集为 `operator_image`。
* 系数矩阵 `CoeffMatrix I = I → I → ENNReal` 输入优先存储：`M i j = M_{i→j}`；
  普通行列显示 `M.display j i = M i j`（第 `j` 行第 `i` 列）。
* 有限族采用 0 基下标：`φ ⟨m,_⟩ = φ_{m+1}`、`L ⟨m,_⟩ = L^{(m+1)}`、
  `imageSeq φ U₁ ⟨m,_⟩ = U_{m+1}`；`chainComp φ = c_k = φ_k ∘ ⋯ ∘ φ_1`，
  `CoeffMatrix.matProd L = L^{(k)} ⋯ L^{(1)}`。
* 路径判据中层数 `n = m + 1`，中间指标序列为 `s : Fin m → I`，完整路径为 `pathOf i j s`。
-/

noncomputable section

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-! ## 0. 规范空间语境 -/

/-- 扩展规范空间 `(𝒳, 𝒢, ⊥)`：有限非空指标集 `I`、吸收元 `bot` 与分量扩展伪度量族 `d`。 -/
structure GaugeSpace (X : Type) (bot : X) (I : Type) [Fintype I] [Nonempty I] where
  /-- 分量伪度量 `d_i`。 -/
  d : I → X → X → ENNReal
  /-- 每个分量满足第 1 章扩展伪度量的四条公理。 -/
  metric : ∀ i, ExtendedPseudoMetric X bot (d i)

namespace GaugeSpace

variable {X : Type} {bot : X} {I : Type} [Fintype I] [Nonempty I] (G : GaugeSpace X bot I)

theorem dist_self (i : I) (x : X) : G.d i x x = 0 := (G.metric i).dist_self x

theorem symm (i : I) (x y : X) : G.d i x y = G.d i y x := (G.metric i).symm x y

theorem triangle (i : I) (x y z : X) : G.d i x z ≤ G.d i x y + G.d i y z :=
  (G.metric i).triangle x y z

end GaugeSpace

/-! ## 1. 系数矩阵 -/

/-- 系数矩阵，输入优先存储：`M i j` 表示 `M_{i→j}`（输入 `i`，输出 `j`）。 -/
abbrev CoeffMatrix (I : Type) := I → I → ENNReal

namespace CoeffMatrix

variable {I : Type}

/-- 复合 `(M₂ · M₁)_{i→j} = ∑ₖ (M₂)_{k→j} (M₁)_{i→k}`。 -/
def comp [Fintype I] (M₂ M₁ : CoeffMatrix I) : CoeffMatrix I :=
  fun i j => ∑ k, M₂ k j * M₁ i k

/-- 单位矩阵 `δ_{ij}`。 -/
def one [DecidableEq I] : CoeffMatrix I := fun i j => if i = j then 1 else 0

/-- 普通行列显示：第 `j` 行第 `i` 列为 `M_{i→j}`。 -/
def display (M : CoeffMatrix I) : Matrix I I ENNReal := Matrix.of fun j i => M i j

@[simp] theorem comp_apply [Fintype I] (M₂ M₁ : CoeffMatrix I) (i j : I) :
    M₂.comp M₁ i j = ∑ k, M₂ k j * M₁ i k := rfl

@[simp] theorem one_apply [DecidableEq I] (i j : I) :
    (one : CoeffMatrix I) i j = if i = j then 1 else 0 := rfl

@[simp] theorem display_apply (M : CoeffMatrix I) (j i : I) : M.display j i = M i j := rfl

theorem display_injective : Function.Injective (display : CoeffMatrix I → Matrix I I ENNReal) := by
  intro M N h
  funext i j
  simpa using congrFun (congrFun h j) i

theorem display_comp [Fintype I] (M₂ M₁ : CoeffMatrix I) :
    (M₂.comp M₁).display = M₂.display * M₁.display := by
  ext j i
  simp [Matrix.mul_apply]

theorem display_one [DecidableEq I] : (one : CoeffMatrix I).display = 1 := by
  ext j i
  simp [Matrix.one_apply, eq_comm]

theorem comp_assoc [Fintype I] (M₃ M₂ M₁ : CoeffMatrix I) :
    M₃.comp (M₂.comp M₁) = (M₃.comp M₂).comp M₁ := by
  apply display_injective
  simp only [display_comp, Matrix.mul_assoc]

theorem comp_one [Fintype I] [DecidableEq I] (M : CoeffMatrix I) : M.comp one = M := by
  apply display_injective
  rw [display_comp, display_one, Matrix.mul_one]

theorem one_comp [Fintype I] [DecidableEq I] (M : CoeffMatrix I) : one.comp M = M := by
  apply display_injective
  rw [display_comp, display_one, Matrix.one_mul]

/-- 有序乘积：`matProd L = L_k ⋯ L_1`（`L ⟨m,_⟩` 为第 `m+1` 步），空乘积为单位矩阵。 -/
def matProd [Fintype I] [DecidableEq I] : {k : ℕ} → (Fin k → CoeffMatrix I) → CoeffMatrix I
  | 0, _ => one
  | _ + 1, L => (L (Fin.last _)).comp (matProd (Fin.init L))

theorem matProd_zero [Fintype I] [DecidableEq I] (L : Fin 0 → CoeffMatrix I) :
    matProd L = one := rfl

theorem matProd_succ [Fintype I] [DecidableEq I] {k : ℕ} (L : Fin (k + 1) → CoeffMatrix I) :
    matProd L = (L (Fin.last k)).comp (matProd (Fin.init L)) := rfl

theorem matProd_one_layer [Fintype I] [DecidableEq I] (L : Fin 1 → CoeffMatrix I) :
    matProd L = L 0 := by
  rw [matProd_succ, matProd_zero, comp_one]
  rfl

theorem display_matProd [Fintype I] [DecidableEq I] {k : ℕ} (L : Fin k → CoeffMatrix I) :
    (matProd L).display = ((List.ofFn L).reverse.map display).prod := by
  induction k with
  | zero => simp [matProd_zero, display_one]
  | succ k ih =>
    rw [matProd_succ, display_comp, ih (Fin.init L), List.ofFn_succ', List.concat_eq_append,
      List.reverse_concat]
    simp
    rfl

end CoeffMatrix

/-! ## 2. 算子复合、有限复合链与实际像域 -/

section Operators

variable {X : Type} {bot : X}

/-- 算子复合 `φ₂ ∘ φ₁`（保持吸收元）。 -/
def opComp (φ₂ φ₁ : Operator X bot) : Operator X bot :=
  ⟨φ₂.func ∘ φ₁.func, by simp [φ₁.preserves_bot, φ₂.preserves_bot]⟩

/-- 恒等算子 `id_𝒳`。 -/
def opId : Operator X bot := ⟨id, rfl⟩

@[simp] theorem opComp_func (φ₂ φ₁ : Operator X bot) (x : X) :
    (opComp φ₂ φ₁).func x = φ₂.func (φ₁.func x) := rfl

@[simp] theorem opId_func (x : X) : (opId : Operator X bot).func x = x := rfl

theorem mem_dom_iff {φ : Operator X bot} {x : X} : x ∈ dom φ ↔ φ.func x ≠ bot := Iff.rfl

theorem dom_opId : dom (opId : Operator X bot) = {x | x ≠ bot} := rfl

/-- 复合定义域：`x ∈ dom(φ₂ ∘ φ₁) ↔ x ∈ dom φ₁ ∧ φ₁ x ∈ dom φ₂`。 -/
theorem mem_dom_opComp {φ₂ φ₁ : Operator X bot} {x : X} :
    x ∈ dom (opComp φ₂ φ₁) ↔ x ∈ dom φ₁ ∧ φ₁.func x ∈ dom φ₂ := by
  simp only [mem_dom_iff, opComp_func]
  constructor
  · intro h
    refine ⟨fun h1 => h ?_, h⟩
    rw [h1, φ₂.preserves_bot]
  · exact fun h => h.2

theorem subset_dom_of_subset_dom_opComp {φ₂ φ₁ : Operator X bot} {U : Set X}
    (h : U ⊆ dom (opComp φ₂ φ₁)) : U ⊆ dom φ₁ :=
  fun _ hx => (mem_dom_opComp.mp (h hx)).1

/-- `U₁ ⊆ dom(φ₂ ∘ φ₁)` 时像集 `U₂ = φ₁(U₁) ⊆ dom φ₂`。 -/
theorem image_subset_dom_of_subset_dom_opComp {φ₂ φ₁ : Operator X bot} {U : Set X}
    (h : U ⊆ dom (opComp φ₂ φ₁)) : operator_image φ₁ U ⊆ dom φ₂ := by
  rintro _ ⟨x, hx, rfl⟩
  exact (mem_dom_opComp.mp (h hx)).2

/-- 有限复合 `c_k = φ_k ∘ ⋯ ∘ φ_1`（`φ ⟨m,_⟩` 为 `φ_{m+1}`），`c_0 = id`。 -/
def chainComp : {k : ℕ} → (Fin k → Operator X bot) → Operator X bot
  | 0, _ => opId
  | _ + 1, φ => opComp (φ (Fin.last _)) (chainComp (Fin.init φ))

theorem chainComp_zero (φ : Fin 0 → Operator X bot) : chainComp φ = opId := rfl

theorem chainComp_succ {k : ℕ} (φ : Fin (k + 1) → Operator X bot) :
    chainComp φ = opComp (φ (Fin.last k)) (chainComp (Fin.init φ)) := rfl

/-- 与第 1 章 `OperatorChain`（列表头最后施行）一致。 -/
theorem chainComp_eq_OperatorChain {k : ℕ} (φ : Fin k → Operator X bot) :
    chainComp φ = OperatorChain (List.ofFn φ).reverse := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [chainComp_succ, ih (Fin.init φ), List.ofFn_succ', List.concat_eq_append,
      List.reverse_concat]
    rfl

/-- 中间像集（自然数下标的递归辅助）。 -/
def imageSeqAux {k : ℕ} (φ : Fin k → Operator X bot) (U₁ : Set X) : ℕ → Set X
  | 0 => U₁
  | m + 1 => if h : m < k then operator_image (φ ⟨m, h⟩) (imageSeqAux φ U₁ m) else ∅

/-- 中间像集 `U_{m+1}`（0 基下标 `⟨m,_⟩`）：`U_1` 给定，`U_{m+1} = φ_m(U_m)`。 -/
def imageSeq {k : ℕ} (φ : Fin k → Operator X bot) (U₁ : Set X) (m : Fin (k + 1)) : Set X :=
  imageSeqAux φ U₁ m

theorem imageSeq_zero {k : ℕ} (φ : Fin k → Operator X bot) (U₁ : Set X) :
    imageSeq φ U₁ 0 = U₁ := rfl

/-- 递归式 `U_{m+1} = φ_m(U_m)`。 -/
theorem imageSeq_succ {k : ℕ} (φ : Fin k → Operator X bot) (U₁ : Set X) (m : Fin k) :
    imageSeq φ U₁ m.succ = operator_image (φ m) (imageSeq φ U₁ m.castSucc) := by
  show imageSeqAux φ U₁ ((m : ℕ) + 1) = _
  rw [imageSeqAux, dif_pos m.isLt]
  rfl

theorem imageSeqAux_init {k : ℕ} (φ : Fin (k + 1) → Operator X bot) (U₁ : Set X) :
    ∀ m : ℕ, m ≤ k → imageSeqAux (Fin.init φ) U₁ m = imageSeqAux φ U₁ m := by
  intro m
  induction m with
  | zero => intro _; rfl
  | succ m ih =>
    intro hm
    have hmk : m < k := hm
    rw [imageSeqAux, imageSeqAux, dif_pos hmk, dif_pos (Nat.lt_succ_of_lt hmk), ih hmk.le]
    rfl

theorem imageSeq_init {k : ℕ} (φ : Fin (k + 1) → Operator X bot) (U₁ : Set X) (m : Fin (k + 1)) :
    imageSeq (Fin.init φ) U₁ m = imageSeq φ U₁ m.castSucc :=
  imageSeqAux_init φ U₁ m (Nat.lt_succ_iff.mp m.isLt)

/-- 全复合像等于逐次像：`U_{k+1} = c_k(U_1)`。 -/
theorem imageSeq_last {k : ℕ} (φ : Fin k → Operator X bot) (U₁ : Set X) :
    imageSeq φ U₁ (Fin.last k) = operator_image (chainComp φ) U₁ := by
  induction k with
  | zero => simp [imageSeq, imageSeqAux, chainComp_zero, operator_image, opId]
  | succ k ih =>
    rw [← Fin.succ_last, imageSeq_succ, ← imageSeq_init, ih (Fin.init φ), chainComp_succ]
    simp only [operator_image, Set.image_image]
    rfl

/-- 每一前缀：`U_{m+1} = c_m(U_1)`（`c_m = φ_m ∘ ⋯ ∘ φ_1`）。 -/
theorem imageSeqAux_eq_prefix {k : ℕ} (φ : Fin k → Operator X bot) (U₁ : Set X) :
    ∀ (m : ℕ) (hm : m ≤ k),
      imageSeqAux φ U₁ m = operator_image (chainComp fun t : Fin m => φ (Fin.castLE hm t)) U₁ := by
  intro m
  induction m with
  | zero => intro _; simp [imageSeqAux, chainComp_zero, operator_image, opId]
  | succ m ih =>
    intro hm
    have hmk : m < k := hm
    rw [imageSeqAux, dif_pos hmk, ih hmk.le, chainComp_succ]
    simp only [operator_image, Set.image_image, opComp_func]
    rfl

theorem imageSeq_eq_prefix {k : ℕ} (φ : Fin k → Operator X bot) (U₁ : Set X) (m : Fin (k + 1)) :
    imageSeq φ U₁ m = operator_image
      (chainComp fun t : Fin m => φ (Fin.castLE (Nat.lt_succ_iff.mp m.isLt) t)) U₁ :=
  imageSeqAux_eq_prefix φ U₁ m _

/-- `U_1 ⊆ dom(c_k)` 蕴含每个 `U_m ⊆ dom(φ_m)`。 -/
theorem imageSeq_subset_dom {k : ℕ} (φ : Fin k → Operator X bot) (U₁ : Set X)
    (hU₁ : U₁ ⊆ dom (chainComp φ)) (m : Fin k) : imageSeq φ U₁ m.castSucc ⊆ dom (φ m) := by
  induction k with
  | zero => exact m.elim0
  | succ k ih =>
    rw [chainComp_succ] at hU₁
    cases m using Fin.lastCases with
    | last =>
      rw [← imageSeq_init, imageSeq_last]
      exact image_subset_dom_of_subset_dom_opComp hU₁
    | cast m =>
      rw [← imageSeq_init]
      exact ih (Fin.init φ) (subset_dom_of_subset_dom_opComp hU₁) m

end Operators

/-! ## 3. Lip / co-Lip 证书族 -/

section Certificates

variable {X : Type} {bot : X} {I : Type} [Fintype I] [Nonempty I] (G : GaugeSpace X bot I)

/-- 全域合法 Lip 矩阵族 `𝓛(φ)`。 -/
def lipSet (φ : Operator X bot) : Set (CoeffMatrix I) :=
  {L | ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j : I,
    G.d j (φ.func x) (φ.func y) ≤ ∑ i, L i j * G.d i x y}

/-- 受限 Lip 矩阵族 `𝓛(φ)|_U`（含 `U ⊆ dom φ`）。 -/
def lipSetOn (φ : Operator X bot) (U : Set X) : Set (CoeffMatrix I) :=
  {L | U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    G.d j (φ.func x) (φ.func y) ≤ ∑ i, L i j * G.d i x y}

/-- 受限 co-Lip 矩阵族 `𝒦(φ)|_U`（含 `U ≠ ∅` 与 `U ⊆ dom φ`）。 -/
def coLipSetOn (φ : Operator X bot) (U : Set X) : Set (CoeffMatrix I) :=
  {K | U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    ∑ i, K i j * G.d i x y ≤ G.d j (φ.func x) (φ.func y)}

theorem lipSet_eq_lipSetOn_dom (φ : Operator X bot) : lipSet G φ = lipSetOn G φ (dom φ) := by
  ext L
  exact ⟨fun h => ⟨subset_rfl, h⟩, fun h => h.2⟩

theorem coLipSetOn_nonempty_iff_ne_empty (φ : Operator X bot) (U : Set X) (K : CoeffMatrix I) :
    K ∈ coLipSetOn G φ U ↔ U ≠ ∅ ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i, K i j * G.d i x y ≤ G.d j (φ.func x) (φ.func y) := by
  simp only [coLipSetOn, Set.mem_setOf_eq, Set.nonempty_iff_ne_empty]

/-- 零矩阵在任意非空 `U ⊆ dom φ` 上是合法 co-Lip 矩阵（`0` 为合法系数）。 -/
theorem zero_mem_coLipSetOn (φ : Operator X bot) {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom φ) : (0 : CoeffMatrix I) ∈ coLipSetOn G φ U :=
  ⟨hne, hU, fun _ _ _ _ _ => by simp⟩

/-- 广义 Lip 约定：`L_{i→j} = ∞` 而 `d_i(x,y) = 0` 时该项贡献为零（`∞ · 0 = 0`）。 -/
theorem top_coeff_term_of_dist_zero {L : CoeffMatrix I} {i j : I} (_h : L i j = ⊤) {x y : X}
    (hd : G.d i x y = 0) : L i j * G.d i x y = 0 := by
  rw [hd, mul_zero]

/-- 广义 Lip 约定：`L_{i→j} = ∞` 且 `d_i(x,y) > 0` 时右端为 `∞`，不等式平凡成立。 -/
theorem lip_ineq_of_top_coeff {φ : Operator X bot} {L : CoeffMatrix I} {i j : I}
    (h : L i j = ⊤) {x y : X} (hd : 0 < G.d i x y) :
    G.d j (φ.func x) (φ.func y) ≤ ∑ k, L k j * G.d k x y := by
  have htop : L i j * G.d i x y = ⊤ := by rw [h, ENNReal.top_mul hd.ne']
  calc G.d j (φ.func x) (φ.func y) ≤ ⊤ := le_top
    _ = L i j * G.d i x y := htop.symm
    _ ≤ ∑ k, L k j * G.d k x y :=
        Finset.single_le_sum (f := fun k => L k j * G.d k x y) (fun _ _ => zero_le _)
          (Finset.mem_univ i)

/-! ### 注 h-c4369c63c86cbacf：单分量情形 -/

/-- 当 `I = {i}` 时 Lip 矩阵条件退化为单个标量不等式（全域版本）。 -/
theorem lipSet_single_component {i : I} (hI : ∀ k : I, k = i) (φ : Operator X bot)
    (L : CoeffMatrix I) :
    L ∈ lipSet G φ ↔
      ∀ x ∈ dom φ, ∀ y ∈ dom φ, G.d i (φ.func x) (φ.func y) ≤ L i i * G.d i x y := by
  have hsum : ∀ (j : I) (x y : X), ∑ k, L k j * G.d k x y = L i i * G.d i x y := by
    intro j x y
    rw [Finset.sum_eq_single i (fun b _ hb => absurd (hI b) hb) (fun h => absurd (Finset.mem_univ i) h),
      hI j]
  constructor
  · intro h x hx y hy
    simpa [hsum] using h x hx y hy i
  · intro h x hx y hy j
    rw [hsum, hI j]
    exact h x hx y hy

/-- 单分量情形的受限版本。 -/
theorem lipSetOn_single_component {i : I} (hI : ∀ k : I, k = i) (φ : Operator X bot)
    (U : Set X) (L : CoeffMatrix I) :
    L ∈ lipSetOn G φ U ↔
      U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, G.d i (φ.func x) (φ.func y) ≤ L i i * G.d i x y := by
  have hsum : ∀ (j : I) (x y : X), ∑ k, L k j * G.d k x y = L i i * G.d i x y := by
    intro j x y
    rw [Finset.sum_eq_single i (fun b _ hb => absurd (hI b) hb) (fun h => absurd (Finset.mem_univ i) h),
      hI j]
  constructor
  · rintro ⟨hU, h⟩
    exact ⟨hU, fun x hx y hy => by simpa [hsum] using h x hx y hy i⟩
  · rintro ⟨hU, h⟩
    refine ⟨hU, fun x hx y hy j => ?_⟩
    rw [hsum, hI j]
    exact h x hx y hy

/-! ### 评估域与证书族 -/

/-- `U ⊆ dom φ` 时 `𝓛(φ) ⊆ 𝓛(φ)|_U`。 -/
theorem lipSet_subset_lipSetOn (φ : Operator X bot) {U : Set X} (hU : U ⊆ dom φ) :
    lipSet G φ ⊆ lipSetOn G φ U :=
  fun _ hL => ⟨hU, fun x hx y hy j => hL x (hU hx) y (hU hy) j⟩

/-- `U ⊆ V ⊆ dom φ` 时 `𝓛(φ)|_V ⊆ 𝓛(φ)|_U`。 -/
theorem lipSetOn_antitone (φ : Operator X bot) {U V : Set X} (hUV : U ⊆ V) (hV : V ⊆ dom φ) :
    lipSetOn G φ V ⊆ lipSetOn G φ U :=
  fun _ hL => ⟨hUV.trans hV, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

/-- 逐条目下确界 `a_{ij}(U) = inf {M_{i→j} : M ∈ 𝓛(φ)|_U}`。 -/
def lipEntryInf (φ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf {c | ∃ M ∈ lipSetOn G φ U, M i j = c}

/-- 评估域缩小时逐条目下确界不增：`U ⊆ V → a_{ij}(U) ≤ a_{ij}(V)`
（`V ⊄ dom φ` 时 `𝓛(φ)|_V = ∅`，右端为 `∞`）。 -/
theorem lipEntryInf_mono (φ : Operator X bot) {U V : Set X} (hUV : U ⊆ V) (i j : I) :
    lipEntryInf G φ U i j ≤ lipEntryInf G φ V i j := by
  apply sInf_le_sInf
  rintro c ⟨M, hM, rfl⟩
  exact ⟨M, lipSetOn_antitone G φ hUV hM.1 hM, rfl⟩

/-! ### 两步复合律 -/

/-- 命题 h-193cebcc1a7f9259（Lip 矩阵复合律）。 -/
theorem lip_comp {φ₁ φ₂ : Operator X bot} {U₁ : Set X} (hU₁ : U₁ ⊆ dom (opComp φ₂ φ₁))
    {L₁ L₂ : CoeffMatrix I} (h₁ : L₁ ∈ lipSetOn G φ₁ U₁)
    (h₂ : L₂ ∈ lipSetOn G φ₂ (operator_image φ₁ U₁)) :
    L₂.comp L₁ ∈ lipSetOn G (opComp φ₂ φ₁) U₁ := by
  refine ⟨hU₁, fun x hx y hy j => ?_⟩
  have hx' : φ₁.func x ∈ operator_image φ₁ U₁ := ⟨x, hx, rfl⟩
  have hy' : φ₁.func y ∈ operator_image φ₁ U₁ := ⟨y, hy, rfl⟩
  calc G.d j ((opComp φ₂ φ₁).func x) ((opComp φ₂ φ₁).func y)
        = G.d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) := rfl
    _ ≤ ∑ k, L₂ k j * G.d k (φ₁.func x) (φ₁.func y) := h₂.2 _ hx' _ hy' j
    _ ≤ ∑ k, L₂ k j * ∑ i, L₁ i k * G.d i x y := by
        gcongr with k
        exact h₁.2 x hx y hy k
    _ = ∑ i, (∑ k, L₂ k j * L₁ i k) * G.d i x y := by
        simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = ∑ i, L₂.comp L₁ i j * G.d i x y := rfl

/-- 命题 h-0f256e6f1d38a612（co-Lip 矩阵复合律）。 -/
theorem coLip_comp {φ₁ φ₂ : Operator X bot} {U₁ : Set X} (hU₁ : U₁ ⊆ dom (opComp φ₂ φ₁))
    {K₁ K₂ : CoeffMatrix I} (h₁ : K₁ ∈ coLipSetOn G φ₁ U₁)
    (h₂ : K₂ ∈ coLipSetOn G φ₂ (operator_image φ₁ U₁)) :
    K₂.comp K₁ ∈ coLipSetOn G (opComp φ₂ φ₁) U₁ := by
  refine ⟨h₁.1, hU₁, fun x hx y hy j => ?_⟩
  have hx' : φ₁.func x ∈ operator_image φ₁ U₁ := ⟨x, hx, rfl⟩
  have hy' : φ₁.func y ∈ operator_image φ₁ U₁ := ⟨y, hy, rfl⟩
  calc ∑ i, K₂.comp K₁ i j * G.d i x y
        = ∑ i, (∑ k, K₂ k j * K₁ i k) * G.d i x y := rfl
    _ = ∑ k, K₂ k j * ∑ i, K₁ i k * G.d i x y := by
        simp_rw [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ ≤ ∑ k, K₂ k j * G.d k (φ₁.func x) (φ₁.func y) := by
        gcongr with k
        exact h₁.2.2 x hx y hy k
    _ ≤ G.d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) := h₂.2.2 _ hx' _ hy' j
    _ = G.d j ((opComp φ₂ φ₁).func x) ((opComp φ₂ φ₁).func y) := rfl

/-! ### 注 h-88784dcbfff0ea66：co-Lip 通道退化 -/

/-- co-Lip 证书中单项给出的下界：`K_{i→j} d_i(x,y) ≤ d_j(φx, φy)`。 -/
theorem coLip_single_term_le {φ : Operator X bot} {U : Set X} {K : CoeffMatrix I}
    (hK : K ∈ coLipSetOn G φ U) (i j : I) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    K i j * G.d i x y ≤ G.d j (φ.func x) (φ.func y) :=
  (Finset.single_le_sum (f := fun k => K k j * G.d k x y) (fun _ _ => zero_le _)
    (Finset.mem_univ i)).trans (hK.2.2 x hx y hy j)

/-- 输出零距而输入正距的点对迫使任一全域 co-Lip 矩阵的 `K_{i→j} = 0`。 -/
theorem coLip_entry_eq_zero_of_pair {φ : Operator X bot} {x y : X} (hx : x ∈ dom φ)
    (hy : y ∈ dom φ) {i j : I} (hout : G.d j (φ.func x) (φ.func y) = 0)
    (hin : 0 < G.d i x y) {K : CoeffMatrix I} (hK : K ∈ coLipSetOn G φ (dom φ)) :
    K i j = 0 := by
  have h := coLip_single_term_le G hK i j hx hy
  rw [hout, nonpos_iff_eq_zero, mul_eq_zero] at h
  exact h.resolve_right hin.ne'

/-! ### 命题 h-b959b42f25710105：两个算子的点对像距扰动界 -/

/-- (i) 正向：`d_j(φ₂x, φ₂y) ≤ d_j(φ₁x, φ₁y) + 2δ_j`。 -/
theorem perturb_forward {φ₁ φ₂ : Operator X bot} {U : Set X} (_hU : U ⊆ dom φ₁ ∩ dom φ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, G.d j (φ₁.func z) (φ₂.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      G.d j (φ₂.func x) (φ₂.func y) ≤ G.d j (φ₁.func x) (φ₁.func y) + 2 * δ j := by
  intro x hx y hy j
  have h1 : G.d j (φ₂.func x) (φ₁.func x) ≤ δ j := by rw [G.symm]; exact hδ x hx j
  have h2 : G.d j (φ₁.func y) (φ₂.func y) ≤ δ j := hδ y hy j
  calc G.d j (φ₂.func x) (φ₂.func y)
        ≤ G.d j (φ₂.func x) (φ₁.func x) + G.d j (φ₁.func x) (φ₂.func y) := G.triangle _ _ _ _
    _ ≤ G.d j (φ₂.func x) (φ₁.func x) +
          (G.d j (φ₁.func x) (φ₁.func y) + G.d j (φ₁.func y) (φ₂.func y)) := by
        gcongr
        exact G.triangle _ _ _ _
    _ ≤ δ j + (G.d j (φ₁.func x) (φ₁.func y) + δ j) := by gcongr
    _ = G.d j (φ₁.func x) (φ₁.func y) + 2 * δ j := by rw [two_mul]; ring

/-- (i) 反向（交换 `φ₁, φ₂`）：`d_j(φ₁x, φ₁y) ≤ d_j(φ₂x, φ₂y) + 2δ_j`。 -/
theorem perturb_backward {φ₁ φ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ₁ ∩ dom φ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, G.d j (φ₁.func z) (φ₂.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      G.d j (φ₁.func x) (φ₁.func y) ≤ G.d j (φ₂.func x) (φ₂.func y) + 2 * δ j :=
  perturb_forward G (φ₁ := φ₂) (φ₂ := φ₁) (fun _ hz => ⟨(hU hz).2, (hU hz).1⟩)
    (fun z hz j => by rw [G.symm]; exact hδ z hz j)

/-- `2δ_j = δ_j + δ_j` 的加法写法（正向）。 -/
theorem perturb_forward_add {φ₁ φ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ₁ ∩ dom φ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, G.d j (φ₁.func z) (φ₂.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      G.d j (φ₂.func x) (φ₂.func y) ≤ G.d j (φ₁.func x) (φ₁.func y) + δ j + δ j := by
  intro x hx y hy j
  rw [add_assoc, ← two_mul]
  exact perturb_forward G hU hδ x hx y hy j

/-- `2δ_j = δ_j + δ_j` 的加法写法（反向）。 -/
theorem perturb_backward_add {φ₁ φ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ₁ ∩ dom φ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, G.d j (φ₁.func z) (φ₂.func z) ≤ δ j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      G.d j (φ₁.func x) (φ₁.func y) ≤ G.d j (φ₂.func x) (φ₂.func y) + δ j + δ j := by
  intro x hx y hy j
  rw [add_assoc, ← two_mul]
  exact perturb_backward G hU hδ x hx y hy j

/-- (ii) Lip 上界桥接。 -/
theorem perturb_lip_bridge {φ₁ φ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ₁ ∩ dom φ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, G.d j (φ₁.func z) (φ₂.func z) ≤ δ j)
    {L₁ : CoeffMatrix I} (hL₁ : L₁ ∈ lipSetOn G φ₁ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      G.d j (φ₂.func x) (φ₂.func y) ≤ ∑ i, L₁ i j * G.d i x y + 2 * δ j := by
  intro x hx y hy j
  calc G.d j (φ₂.func x) (φ₂.func y) ≤ G.d j (φ₁.func x) (φ₁.func y) + 2 * δ j :=
        perturb_forward G hU hδ x hx y hy j
    _ ≤ ∑ i, L₁ i j * G.d i x y + 2 * δ j := by
        gcongr
        exact hL₁.2 x hx y hy j

/-- (iii) co-Lip 下界桥接。 -/
theorem perturb_coLip_bridge {φ₁ φ₂ : Operator X bot} {U : Set X} (hU : U ⊆ dom φ₁ ∩ dom φ₂)
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, G.d j (φ₁.func z) (φ₂.func z) ≤ δ j)
    {K₁ : CoeffMatrix I} (hK₁ : K₁ ∈ coLipSetOn G φ₁ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i, K₁ i j * G.d i x y ≤ G.d j (φ₂.func x) (φ₂.func y) + 2 * δ j := by
  intro x hx y hy j
  exact (hK₁.2.2 x hx y hy j).trans (perturb_backward G hU hδ x hx y hy j)

/-- 交换 `φ₁, φ₂`：`φ₂` 的 Lip 证书对 `φ₁` 的桥接。 -/
theorem perturb_lip_bridge_swap {φ₁ φ₂ : Operator X bot} {U : Set X}
    (hU : U ⊆ dom φ₁ ∩ dom φ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, G.d j (φ₁.func z) (φ₂.func z) ≤ δ j)
    {L₂ : CoeffMatrix I} (hL₂ : L₂ ∈ lipSetOn G φ₂ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      G.d j (φ₁.func x) (φ₁.func y) ≤ ∑ i, L₂ i j * G.d i x y + 2 * δ j := by
  intro x hx y hy j
  calc G.d j (φ₁.func x) (φ₁.func y) ≤ G.d j (φ₂.func x) (φ₂.func y) + 2 * δ j :=
        perturb_backward G hU hδ x hx y hy j
    _ ≤ ∑ i, L₂ i j * G.d i x y + 2 * δ j := by
        gcongr
        exact hL₂.2 x hx y hy j

/-- 交换 `φ₁, φ₂`：`φ₂` 的 co-Lip 证书对 `φ₁` 的桥接。 -/
theorem perturb_coLip_bridge_swap {φ₁ φ₂ : Operator X bot} {U : Set X}
    (hU : U ⊆ dom φ₁ ∩ dom φ₂) {δ : I → ENNReal}
    (hδ : ∀ z ∈ U, ∀ j, G.d j (φ₁.func z) (φ₂.func z) ≤ δ j)
    {K₂ : CoeffMatrix I} (hK₂ : K₂ ∈ coLipSetOn G φ₂ U) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      ∑ i, K₂ i j * G.d i x y ≤ G.d j (φ₁.func x) (φ₁.func y) + 2 * δ j := by
  intro x hx y hy j
  exact (hK₂.2.2 x hx y hy j).trans (perturb_forward G hU hδ x hx y hy j)

/-! ### 注 h-11006ddd8c43bfec：零步复合的单位矩阵证书 -/

theorem sum_one_mul [DecidableEq I] (j : I) (x y : X) :
    ∑ i, (CoeffMatrix.one : CoeffMatrix I) i j * G.d i x y = G.d j x y := by
  simp [CoeffMatrix.one_apply]

/-- 非空 `U ⊆ dom(id)` 上单位矩阵是 `id` 的合法 Lip 矩阵。 -/
theorem one_mem_lipSetOn_opId [DecidableEq I] {U : Set X} (_hne : U.Nonempty)
    (hU : U ⊆ dom (opId : Operator X bot)) : CoeffMatrix.one ∈ lipSetOn G opId U :=
  ⟨hU, fun x _ y _ j => by rw [sum_one_mul]; rfl⟩

/-- 非空 `U ⊆ dom(id)` 上单位矩阵是 `id` 的合法 co-Lip 矩阵。 -/
theorem one_mem_coLipSetOn_opId [DecidableEq I] {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (opId : Operator X bot)) : CoeffMatrix.one ∈ coLipSetOn G opId U :=
  ⟨hne, hU, fun x _ y _ j => by rw [sum_one_mul]; rfl⟩

/-- 同一单位矩阵同时属于 `𝓛(id)|_U ∩ 𝒦(id)|_U`。 -/
theorem one_mem_lipSetOn_inter_coLipSetOn_opId [DecidableEq I] {U : Set X} (hne : U.Nonempty)
    (hU : U ⊆ dom (opId : Operator X bot)) :
    CoeffMatrix.one ∈ lipSetOn G opId U ∩ coLipSetOn G opId U :=
  ⟨one_mem_lipSetOn_opId G hne hU, one_mem_coLipSetOn_opId G hne hU⟩

/-- 零步链形式：`c_0 = id`，空乘积 `= I`，二者给出 Lip 与 co-Lip 证书。 -/
theorem zero_step_chain_certificate [DecidableEq I] (φ : Fin 0 → Operator X bot)
    (L : Fin 0 → CoeffMatrix I) {U : Set X} (hne : U.Nonempty) (hU : U ⊆ dom (chainComp φ)) :
    chainComp φ = opId ∧ CoeffMatrix.matProd L = CoeffMatrix.one ∧
      CoeffMatrix.matProd L ∈ lipSetOn G (chainComp φ) U ∩ coLipSetOn G (chainComp φ) U :=
  ⟨rfl, rfl, one_mem_lipSetOn_inter_coLipSetOn_opId G hne hU⟩

/-! ### 推论 h-c80171fa685dc795：有限复合的局部矩阵界 -/

/-- Lip 链：对任意长度 `k`（含 `k = 0`），逐步实际输入域上的证书之积是全复合证书。 -/
theorem lip_chain_any_length [DecidableEq I] {k : ℕ} (φ : Fin k → Operator X bot) (U₁ : Set X)
    (hU₁ : U₁ ⊆ dom (chainComp φ)) (L : Fin k → CoeffMatrix I)
    (hL : ∀ m : Fin k, L m ∈ lipSetOn G (φ m) (imageSeq φ U₁ m.castSucc)) :
    CoeffMatrix.matProd L ∈ lipSetOn G (chainComp φ) U₁ := by
  induction k with
  | zero =>
    refine ⟨hU₁, fun x _ y _ j => ?_⟩
    rw [CoeffMatrix.matProd_zero, sum_one_mul]
    rfl
  | succ k ih =>
    rw [chainComp_succ] at hU₁ ⊢
    rw [CoeffMatrix.matProd_succ]
    have hinit : CoeffMatrix.matProd (Fin.init L) ∈ lipSetOn G (chainComp (Fin.init φ)) U₁ :=
      ih (Fin.init φ) (subset_dom_of_subset_dom_opComp hU₁) (Fin.init L)
        (fun m => by rw [imageSeq_init]; exact hL m.castSucc)
    have hlast : L (Fin.last k) ∈
        lipSetOn G (φ (Fin.last k)) (operator_image (chainComp (Fin.init φ)) U₁) := by
      rw [← imageSeq_last, imageSeq_init]
      exact hL (Fin.last k)
    exact lip_comp G hU₁ hinit hlast

/-- (i) Lip 矩阵放缩上限（正文 `k ≥ 1`）。 -/
theorem lip_chain {k : ℕ} [DecidableEq I] (_hk : 1 ≤ k) (φ : Fin k → Operator X bot) (U₁ : Set X)
    (hU₁ : U₁ ⊆ dom (chainComp φ)) (L : Fin k → CoeffMatrix I)
    (hL : ∀ m : Fin k, L m ∈ lipSetOn G (φ m) (imageSeq φ U₁ m.castSucc)) :
    CoeffMatrix.matProd L ∈ lipSetOn G (chainComp φ) U₁ :=
  lip_chain_any_length G φ U₁ hU₁ L hL

/-- co-Lip 链（任意长度，`U₁` 非空）。 -/
theorem coLip_chain_of_nonempty [DecidableEq I] {k : ℕ} (φ : Fin k → Operator X bot) (U₁ : Set X)
    (hne : U₁.Nonempty) (hU₁ : U₁ ⊆ dom (chainComp φ)) (K : Fin k → CoeffMatrix I)
    (hK : ∀ m : Fin k, K m ∈ coLipSetOn G (φ m) (imageSeq φ U₁ m.castSucc)) :
    CoeffMatrix.matProd K ∈ coLipSetOn G (chainComp φ) U₁ := by
  induction k with
  | zero =>
    refine ⟨hne, hU₁, fun x _ y _ j => ?_⟩
    rw [CoeffMatrix.matProd_zero, sum_one_mul]
    rfl
  | succ k ih =>
    rw [chainComp_succ] at hU₁ ⊢
    rw [CoeffMatrix.matProd_succ]
    have hinit : CoeffMatrix.matProd (Fin.init K) ∈ coLipSetOn G (chainComp (Fin.init φ)) U₁ :=
      ih (Fin.init φ) (subset_dom_of_subset_dom_opComp hU₁) (Fin.init K)
        (fun m => by rw [imageSeq_init]; exact hK m.castSucc)
    have hlast : K (Fin.last k) ∈
        coLipSetOn G (φ (Fin.last k)) (operator_image (chainComp (Fin.init φ)) U₁) := by
      rw [← imageSeq_last, imageSeq_init]
      exact hK (Fin.last k)
    exact coLip_comp G hU₁ hinit hlast

/-- (ii) co-Lip 矩阵保距下限（正文 `k ≥ 1`；`U₁` 的非空性来自第一步证书）。 -/
theorem coLip_chain {k : ℕ} [DecidableEq I] (hk : 1 ≤ k) (φ : Fin k → Operator X bot)
    (U₁ : Set X) (hU₁ : U₁ ⊆ dom (chainComp φ)) (K : Fin k → CoeffMatrix I)
    (hK : ∀ m : Fin k, K m ∈ coLipSetOn G (φ m) (imageSeq φ U₁ m.castSucc)) :
    CoeffMatrix.matProd K ∈ coLipSetOn G (chainComp φ) U₁ := by
  have hne : U₁.Nonempty := by
    have h0 := (hK ⟨0, hk⟩).1
    rwa [show (⟨0, hk⟩ : Fin k).castSucc = 0 from rfl, imageSeq_zero] at h0
  exact coLip_chain_of_nonempty G φ U₁ hne hU₁ K hK

/-- 带逐步局部 Lip 证书的有限复合链：字段只含逐步数据（算子、起始域、逐步矩阵、
各实际输入域上的单步界），不含全复合界。 -/
structure LipStepChain (k : ℕ) where
  /-- 施行顺序的算子 `φ_1, …, φ_k`。 -/
  ops : Fin k → Operator X bot
  /-- 起始域 `U_1`。 -/
  start : Set X
  /-- `U_1 ⊆ dom(c_k)`。 -/
  start_subset : start ⊆ dom (chainComp ops)
  /-- 逐步矩阵 `L^{(1)}, …, L^{(k)}`。 -/
  mats : Fin k → CoeffMatrix I
  /-- 第 `m` 步在实际输入域 `U_m` 上合法。 -/
  step_mem : ∀ m : Fin k, mats m ∈ lipSetOn G (ops m) (imageSeq ops start m.castSucc)

/-- 带逐步局部 co-Lip 证书的有限复合链（`k ≥ 1`）；字段只含逐步数据。 -/
structure CoLipStepChain (k : ℕ) where
  /-- 链长 `k ≥ 1`。 -/
  length_pos : 1 ≤ k
  /-- 施行顺序的算子 `φ_1, …, φ_k`。 -/
  ops : Fin k → Operator X bot
  /-- 起始域 `U_1`。 -/
  start : Set X
  /-- `U_1 ⊆ dom(c_k)`。 -/
  start_subset : start ⊆ dom (chainComp ops)
  /-- 逐步矩阵 `K^{(1)}, …, K^{(k)}`。 -/
  mats : Fin k → CoeffMatrix I
  /-- 第 `m` 步在实际输入域 `U_m` 上合法（含非空性）。 -/
  step_mem : ∀ m : Fin k, mats m ∈ coLipSetOn G (ops m) (imageSeq ops start m.castSucc)

namespace LipStepChain

variable {G} {k : ℕ} (C : LipStepChain G k)

/-- 目标链的全复合 `c_k`。 -/
def composite : Operator X bot := chainComp C.ops

/-- 目标链的矩阵乘积 `L^{(k)} ⋯ L^{(1)}`。 -/
def product [DecidableEq I] : CoeffMatrix I := CoeffMatrix.matProd C.mats

theorem product_mem [DecidableEq I] : C.product ∈ lipSetOn G C.composite C.start :=
  lip_chain_any_length G C.ops C.start C.start_subset C.mats C.step_mem

end LipStepChain

namespace CoLipStepChain

variable {G} {k : ℕ} (C : CoLipStepChain G k)

/-- 目标链的全复合 `c_k`。 -/
def composite : Operator X bot := chainComp C.ops

/-- 目标链的矩阵乘积 `K^{(k)} ⋯ K^{(1)}`。 -/
def product [DecidableEq I] : CoeffMatrix I := CoeffMatrix.matProd C.mats

theorem product_mem [DecidableEq I] : C.product ∈ coLipSetOn G C.composite C.start :=
  coLip_chain G C.length_pos C.ops C.start C.start_subset C.mats C.step_mem

end CoLipStepChain

end Certificates

/-! ## 4. 有限矩阵乘积条目的路径展开 -/

section Paths

variable {I : Type}

/-- 完整指标路径 `(k_0, k_1, …, k_{m}, k_{m+1}) = (i, s_0, …, s_{m-1}, j)`；
层数 `n = m + 1`，中间序列 `s : Fin m → I` 无任何正性约束。 -/
def pathOf {m : ℕ} (i j : I) (s : Fin m → I) : Fin (m + 2) → I :=
  Fin.snoc (α := fun _ => I) (Fin.cons (α := fun _ => I) i s) j

@[simp] theorem pathOf_zero {m : ℕ} (i j : I) (s : Fin m → I) : pathOf i j s 0 = i := by
  show Fin.snoc (α := fun _ => I) (Fin.cons (α := fun _ => I) i s) j (Fin.castSucc 0) = i
  rw [Fin.snoc_castSucc]
  rfl

@[simp] theorem pathOf_last {m : ℕ} (i j : I) (s : Fin m → I) :
    pathOf i j s (Fin.last (m + 1)) = j := by
  simp [pathOf]

/-- 中间位置 `k_{u+1} = s u`。 -/
@[simp] theorem pathOf_inner {m : ℕ} (i j : I) (s : Fin m → I) (u : Fin m) :
    pathOf i j s u.succ.castSucc = s u := by
  unfold pathOf
  rw [Fin.snoc_castSucc]
  rfl

theorem pathOf_snoc {m : ℕ} (i j k : I) (s : Fin m → I) :
    pathOf i j (Fin.snoc (α := fun _ => I) s k) = Fin.snoc (α := fun _ => I) (pathOf i k s) j := by
  unfold pathOf
  rw [Fin.cons_snoc_eq_snoc_cons]

/-- `n = 1` 时只有唯一的空中间序列，对应路径 `(i, j)`。 -/
theorem pathOf_one_layer (i j : I) (s : Fin 0 → I) :
    pathOf i j s 0 = i ∧ pathOf i j s 1 = j :=
  ⟨pathOf_zero i j s, pathOf_last i j s⟩

/-- `n = 1` 时中间序列只有一个（空序列）。 -/
theorem card_intermediate_one_layer [Fintype I] [DecidableEq I] :
    Fintype.card (Fin 0 → I) = 1 := by
  simp

theorem intermediate_one_layer_eq (s t : Fin 0 → I) : s = t := Subsingleton.elim s t

/-- 路径第 `t+1` 层的边条目 `[L^{(t+1)}]_{k_t → k_{t+1}}`。 -/
def pathEdge {m : ℕ} (L : Fin (m + 1) → CoeffMatrix I) (i j : I) (s : Fin m → I)
    (t : Fin (m + 1)) : ENNReal :=
  L t (pathOf i j s t.castSucc) (pathOf i j s t.succ)

/-- 路径权重：各层条目之积。 -/
def pathWeight {m : ℕ} (L : Fin (m + 1) → CoeffMatrix I) (i j : I) (s : Fin m → I) : ENNReal :=
  ∏ t : Fin (m + 1), pathEdge L i j s t

/-- 含零：某一层边条目为 `0`。 -/
def PathHasZeroEdge {m : ℕ} (L : Fin (m + 1) → CoeffMatrix I) (i j : I) (s : Fin m → I) : Prop :=
  ∃ t : Fin (m + 1), pathEdge L i j s t = 0

/-- 全正：每一层边条目都 `> 0`。 -/
def PathAllPositive {m : ℕ} (L : Fin (m + 1) → CoeffMatrix I) (i j : I) (s : Fin m → I) : Prop :=
  ∀ t : Fin (m + 1), 0 < pathEdge L i j s t

theorem pathWeight_snoc {m : ℕ} (L : Fin (m + 2) → CoeffMatrix I) (i j k : I) (s : Fin m → I) :
    pathWeight L i j (Fin.snoc (α := fun _ => I) s k) =
      pathWeight (Fin.init L) i k s * L (Fin.last (m + 1)) k j := by
  unfold pathWeight pathEdge
  rw [pathOf_snoc, Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl (fun u _ => ?_)
    rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl
  · rw [Fin.snoc_castSucc, pathOf_last, Fin.succ_last, Fin.snoc_last]

/-- `n = 1` 时路径判据与单条目判据一致（唯一空中间序列）。 -/
theorem pathHasZeroEdge_one_layer_iff (L : Fin 1 → CoeffMatrix I) (i j : I) (s : Fin 0 → I) :
    PathHasZeroEdge L i j s ↔ L 0 i j = 0 := by
  simp [PathHasZeroEdge, pathEdge]
  rfl

theorem pathAllPositive_one_layer_iff (K : Fin 1 → CoeffMatrix I) (i j : I) (s : Fin 0 → I) :
    PathAllPositive K i j s ↔ 0 < K 0 i j := by
  simp [PathAllPositive, pathEdge]
  rfl

variable [Fintype I] [DecidableEq I]

/-- 乘积条目的路径展开：`(L_n ⋯ L_1)_{i→j} = ∑_{中间序列} ∏ 各层条目`（`n = m + 1`）。 -/
theorem matProd_apply_eq_sum_pathWeight {m : ℕ} (L : Fin (m + 1) → CoeffMatrix I) (i j : I) :
    CoeffMatrix.matProd L i j = ∑ s : Fin m → I, pathWeight L i j s := by
  induction m generalizing j with
  | zero =>
    rw [CoeffMatrix.matProd_one_layer, Fintype.sum_unique]
    simp [pathWeight, pathEdge]
    rfl
  | succ m ih =>
    rw [CoeffMatrix.matProd_succ, CoeffMatrix.comp_apply]
    rw [← Fintype.sum_equiv (Fin.snocEquiv (fun _ => I)) _ _ (fun _ => rfl),
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [ih (Fin.init L) k, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    change _ = pathWeight L i j (Fin.snoc (α := fun _ => I) s k)
    rw [pathWeight_snoc, mul_comm]

/-- 命题 h-e4154c34e95d3c23 (i) 的代数核心：乘积条目为零 iff 每条完整路径含零边。 -/
theorem matProd_apply_eq_zero_iff {m : ℕ} (L : Fin (m + 1) → CoeffMatrix I) (i j : I) :
    CoeffMatrix.matProd L i j = 0 ↔ ∀ s : Fin m → I, PathHasZeroEdge L i j s := by
  rw [matProd_apply_eq_sum_pathWeight, Finset.sum_eq_zero_iff]
  simp only [Finset.mem_univ, true_implies, pathWeight, Finset.prod_eq_zero_iff, true_and,
    PathHasZeroEdge]

/-- 命题 h-e4154c34e95d3c23 (ii) 的代数核心：乘积条目为正 iff 存在一条全正路径。 -/
theorem matProd_apply_pos_iff {m : ℕ} (K : Fin (m + 1) → CoeffMatrix I) (i j : I) :
    0 < CoeffMatrix.matProd K i j ↔ ∃ s : Fin m → I, PathAllPositive K i j s := by
  rw [pos_iff_ne_zero, Ne, matProd_apply_eq_zero_iff]
  simp only [PathHasZeroEdge, PathAllPositive, not_forall, not_exists, pos_iff_ne_zero, Ne]

/-- `n = 1` 退化：`[L^{(1)}]_{i→j} = 0`。 -/
theorem matProd_one_layer_eq_zero_iff (L : Fin 1 → CoeffMatrix I) (i j : I) :
    CoeffMatrix.matProd L i j = 0 ↔ L 0 i j = 0 := by
  rw [CoeffMatrix.matProd_one_layer]

/-- `n = 1` 退化：`[K^{(1)}]_{i→j} > 0`。 -/
theorem matProd_one_layer_pos_iff (K : Fin 1 → CoeffMatrix I) (i j : I) :
    0 < CoeffMatrix.matProd K i j ↔ 0 < K 0 i j := by
  rw [CoeffMatrix.matProd_one_layer]

end Paths

section PathCriteria

variable {X : Type} {bot : X} {I : Type} [Fintype I] [Nonempty I] [DecidableEq I]
  (G : GaugeSpace X bot I)

/-- 命题 h-e4154c34e95d3c23 (i)：沿非空复合链 `c_n`（`n = m + 1`）取实际像域上的 Lip 证书，
`[L^{(n)} ⋯ L^{(1)}]_{i→j} = 0` iff 每个中间指标序列都含零边。 -/
theorem lip_chain_entry_eq_zero_iff {m : ℕ} (φ : Fin (m + 1) → Operator X bot) (U₁ : Set X)
    (_hU₁ : U₁ ⊆ dom (chainComp φ)) (L : Fin (m + 1) → CoeffMatrix I)
    (_hL : ∀ t : Fin (m + 1), L t ∈ lipSetOn G (φ t) (imageSeq φ U₁ t.castSucc)) (i j : I) :
    CoeffMatrix.matProd L i j = 0 ↔ ∀ s : Fin m → I, PathHasZeroEdge L i j s :=
  matProd_apply_eq_zero_iff L i j

/-- 命题 h-e4154c34e95d3c23 (ii)：同一链上的 co-Lip 证书，
`[K^{(n)} ⋯ K^{(1)}]_{i→j} > 0` iff 存在一条全正路径。 -/
theorem coLip_chain_entry_pos_iff {m : ℕ} (φ : Fin (m + 1) → Operator X bot) (U₁ : Set X)
    (_hU₁ : U₁ ⊆ dom (chainComp φ)) (K : Fin (m + 1) → CoeffMatrix I)
    (_hK : ∀ t : Fin (m + 1), K t ∈ coLipSetOn G (φ t) (imageSeq φ U₁ t.castSucc)) (i j : I) :
    0 < CoeffMatrix.matProd K i j ↔ ∃ s : Fin m → I, PathAllPositive K i j s :=
  matProd_apply_pos_iff K i j

/-- 正文同时选取 `L^{(m)}` 与 `K^{(m)}` 的合并形式。 -/
theorem chain_entry_criteria {m : ℕ} (φ : Fin (m + 1) → Operator X bot) (U₁ : Set X)
    (hU₁ : U₁ ⊆ dom (chainComp φ)) (L K : Fin (m + 1) → CoeffMatrix I)
    (hL : ∀ t : Fin (m + 1), L t ∈ lipSetOn G (φ t) (imageSeq φ U₁ t.castSucc))
    (hK : ∀ t : Fin (m + 1), K t ∈ coLipSetOn G (φ t) (imageSeq φ U₁ t.castSucc)) (i j : I) :
    (CoeffMatrix.matProd L i j = 0 ↔ ∀ s : Fin m → I, PathHasZeroEdge L i j s) ∧
      (0 < CoeffMatrix.matProd K i j ↔ ∃ s : Fin m → I, PathAllPositive K i j s) :=
  ⟨lip_chain_entry_eq_zero_iff G φ U₁ hU₁ L hL i j, coLip_chain_entry_pos_iff G φ U₁ hU₁ K hK i j⟩

end PathCriteria

/-! ## 5. 分量解耦与通道分辨保持（h-7fa97eb6e24d5527） -/

section Channels

variable {I : Type}

/-- 分量通道：从输入分量 `d_i` 到输出分量 `d_j` 的有序对 `(i, j) ∈ I × I`。 -/
abbrev Channel (I : Type) := I × I

/-- 单行稀疏：第 `j` 行（输出 `j`）除输入位置 `i` 外全为零。 -/
def RowSparse (L : CoeffMatrix I) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0

/-- 单列稀疏：第 `i` 列（输入 `i`）除输出位置 `j` 外全为零。 -/
def ColSparse (L : CoeffMatrix I) (i j : I) : Prop := ∀ k, k ≠ j → L i k = 0

/-- 对角：所有非对角条目为零。 -/
def IsDiagonal (L : CoeffMatrix I) : Prop := ∀ i j, i ≠ j → L i j = 0

/-- 行稀疏即显示矩阵第 `j` 行仅第 `i` 列可能非零。 -/
theorem rowSparse_iff_display (L : CoeffMatrix I) (i j : I) :
    RowSparse L i j ↔ ∀ k, k ≠ i → L.display j k = 0 := Iff.rfl

/-- 列稀疏即显示矩阵第 `i` 列仅第 `j` 行可能非零。 -/
theorem colSparse_iff_display (L : CoeffMatrix I) (i j : I) :
    ColSparse L i j ↔ ∀ k, k ≠ j → L.display k i = 0 := Iff.rfl

/-- “第 `j` 行至多有一项非零”与 `∃ i, RowSparse L i j` 等价。 -/
theorem exists_rowSparse_iff_subsingleton [Nonempty I] (L : CoeffMatrix I) (j : I) :
    (∃ i, RowSparse L i j) ↔ {k | L k j ≠ 0}.Subsingleton := by
  constructor
  · rintro ⟨i, hi⟩ a ha b hb
    by_contra hab
    by_cases hai : a = i
    · exact hb (hi b (fun hbi => hab (hai.trans hbi.symm)))
    · exact ha (hi a hai)
  · intro h
    by_cases hex : ∃ i, L i j ≠ 0
    · obtain ⟨i, hi⟩ := hex
      exact ⟨i, fun k hk => by_contra fun hkj => hk (h hkj hi)⟩
    · push Not at hex
      exact ⟨Classical.arbitrary I, fun k _ => hex k⟩

/-- “第 `i` 列至多有一项非零”与 `∃ j, ColSparse L i j` 等价。 -/
theorem exists_colSparse_iff_subsingleton [Nonempty I] (L : CoeffMatrix I) (i : I) :
    (∃ j, ColSparse L i j) ↔ {k | L i k ≠ 0}.Subsingleton := by
  constructor
  · rintro ⟨j, hj⟩ a ha b hb
    by_contra hab
    by_cases haj : a = j
    · exact hb (hj b (fun hbj => hab (haj.trans hbj.symm)))
    · exact ha (hj a haj)
  · intro h
    by_cases hex : ∃ j, L i j ≠ 0
    · obtain ⟨j, hj⟩ := hex
      exact ⟨j, fun k hk => by_contra fun hik => hk (h hik hj)⟩
    · push Not at hex
      exact ⟨Classical.arbitrary I, fun k _ => hex k⟩

theorem isDiagonal_iff_rowSparse (L : CoeffMatrix I) :
    IsDiagonal L ↔ ∀ j, RowSparse L j j :=
  ⟨fun h j k hk => h k j hk, fun h i j hij => h j i hij⟩

end Channels

section ChannelBounds

variable {X : Type} {bot : X} {I : Type} [Fintype I] [Nonempty I] (G : GaugeSpace X bot I)

/-- 行解耦：存在 `L ∈ 𝓛(φ)|_U` 使第 `j` 行至多一项非零。 -/
def RowDecoupled (φ : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ L ∈ lipSetOn G φ U, ∃ i, RowSparse L i j

/-- 列解耦：存在 `L ∈ 𝓛(φ)|_U` 使第 `i` 列至多一项非零。 -/
def ColDecoupled (φ : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ L ∈ lipSetOn G φ U, ∃ j, ColSparse L i j

/-- 完全解耦体系：所选上界证书为对角矩阵。 -/
def FullyDecoupledCertificate (φ : Operator X bot) (U : Set X) (L : CoeffMatrix I) : Prop :=
  L ∈ lipSetOn G φ U ∧ IsDiagonal L

/-! ### 单通道 Lip 常数 -/

/-- 单通道可行常数集 `S_{ij} = {λ ∈ [0,∞] : ∀ x y ∈ U, d_j(φx,φy) ≤ λ · d_i(x,y)}`。 -/
def scalarFeasible (φ : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  {c | ∀ x ∈ U, ∀ y ∈ U, G.d j (φ.func x) (φ.func y) ≤ c * G.d i x y}

/-- 单通道 Lip 常数 `L̲_{i→j}(φ;U) = inf S_{ij}`（`inf ∅ = ∞`）。 -/
def channelLip (φ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (scalarFeasible G φ U i j)

/-- 以分量通道 `(i, j) : Channel I` 为参数的单通道 Lip 常数。 -/
def channelLipAt (φ : Operator X bot) (U : Set X) (c : Channel I) : ENNReal :=
  channelLip G φ U c.1 c.2

theorem channelLip_empty_feasible {φ : Operator X bot} {U : Set X} {i j : I}
    (h : scalarFeasible G φ U i j = ∅) : channelLip G φ U i j = ⊤ := by
  rw [channelLip, h, sInf_empty]

/-- 零输入距、正输出距的点对使可行集为空，从而 `L̲_{i→j} = ∞`。 -/
theorem scalarFeasible_eq_empty_of_pair {φ : Operator X bot} {U : Set X} {i j : I} {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (hin : G.d i x y = 0) (hout : 0 < G.d j (φ.func x) (φ.func y)) :
    (∀ c : ENNReal, c ∉ scalarFeasible G φ U i j) ∧ channelLip G φ U i j = ⊤ := by
  have hno : ∀ c : ENNReal, c ∉ scalarFeasible G φ U i j := by
    intro c hc
    have h := hc x hx y hy
    rw [hin, mul_zero] at h
    exact (not_le.mpr hout) h
  refine ⟨hno, channelLip_empty_feasible G ?_⟩
  exact Set.eq_empty_iff_forall_notMem.mpr hno

/-- 可行常数集向上封闭。 -/
theorem scalarFeasible_upward {φ : Operator X bot} {U : Set X} {i j : I} {c₀ c₁ : ENNReal}
    (h₀ : c₀ ∈ scalarFeasible G φ U i j) (h : c₀ ≤ c₁) : c₁ ∈ scalarFeasible G φ U i j :=
  fun x hx y hy => (h₀ x hx y hy).trans (mul_le_mul_left h _)

/-- 严格大于下确界的每个常数（允许 `∞`）都可行。 -/
theorem mem_scalarFeasible_of_channelLip_lt {φ : Operator X bot} {U : Set X} {i j : I}
    {c : ENNReal} (hc : channelLip G φ U i j < c) : c ∈ scalarFeasible G φ U i j := by
  obtain ⟨c₀, hc₀, hlt⟩ := sInf_lt_iff.mp hc
  exact scalarFeasible_upward G hc₀ hlt.le

/-- 正文语境 `0 < a < ∞` 下：任意 `λ > a`（允许 `λ = ∞`）属于 `S`。 -/
theorem mem_scalarFeasible_of_gt_in_context {φ : Operator X bot} {U : Set X} {i j : I} :
    0 < channelLip G φ U i j → channelLip G φ U i j < ⊤ →
      ∀ c : ENNReal, channelLip G φ U i j < c → c ∈ scalarFeasible G φ U i j :=
  fun _ _ _ hc => mem_scalarFeasible_of_channelLip_lt G hc

/-- 正有限下确界可被取到：`0 < a < ∞ → a ∈ S`。 -/
theorem channelLip_mem_scalarFeasible {φ : Operator X bot} {U : Set X} {i j : I}
    (hpos : 0 < channelLip G φ U i j) (hfin : channelLip G φ U i j < ⊤) :
    channelLip G φ U i j ∈ scalarFeasible G φ U i j := by
  set a := channelLip G φ U i j
  intro x hx y hy
  set A := G.d j (φ.func x) (φ.func y)
  set B := G.d i x y
  have hgt : ∀ c, a < c → A ≤ c * B := fun c hc =>
    mem_scalarFeasible_of_channelLip_lt G hc x hx y hy
  by_cases hB0 : B = 0
  · have h := hgt ⊤ hfin
    rw [hB0, mul_zero] at h
    rw [hB0, mul_zero]
    exact h
  by_cases hBtop : B = ⊤
  · rw [hBtop, ENNReal.mul_top hpos.ne']
    exact le_top
  · by_contra hlt
    push Not at hlt
    have h1 : a < A / B := (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mpr hlt
    obtain ⟨c, hac, hcA⟩ := exists_between h1
    have h2 : c * B < A := (ENNReal.lt_div_iff_mul_lt (Or.inl hB0) (Or.inl hBtop)).mp hcA
    exact (not_le.mpr h2) (hgt c hac)

/-- 正有限下确界取到的点对形式。 -/
theorem channelLip_bound {φ : Operator X bot} {U : Set X} {i j : I}
    (hpos : 0 < channelLip G φ U i j) (hfin : channelLip G φ U i j < ⊤) :
    ∀ x ∈ U, ∀ y ∈ U, G.d j (φ.func x) (φ.func y) ≤ channelLip G φ U i j * G.d i x y :=
  channelLip_mem_scalarFeasible G hpos hfin

/-- 零下确界：每个有限正数 `λ` 都是标量证书。 -/
theorem mem_scalarFeasible_of_channelLip_eq_zero {φ : Operator X bot} {U : Set X} {i j : I}
    (h0 : channelLip G φ U i j = 0) :
    ∀ c : ENNReal, 0 < c → c < ⊤ → c ∈ scalarFeasible G φ U i j :=
  fun _ hc _ => mem_scalarFeasible_of_channelLip_lt G (h0 ▸ hc)

/-- `L̲_{i→j} < ∞` iff 存在有限可行常数。 -/
theorem channelLip_lt_top_iff {φ : Operator X bot} {U : Set X} {i j : I} :
    channelLip G φ U i j < ⊤ ↔ ∃ c : ENNReal, c < ⊤ ∧ c ∈ scalarFeasible G φ U i j := by
  constructor
  · intro h
    obtain ⟨c, hc, hlt⟩ := sInf_lt_iff.mp h
    exact ⟨c, hlt, hc⟩
  · rintro ⟨c, hc, hmem⟩
    exact (sInf_le hmem).trans_lt hc

/-! ### 通道隔离、行/列解耦、完全解耦 -/

/-- 零系数项为零（允许 `d_i = ∞`，因 `0 · ∞ = 0`）。 -/
theorem zero_coeff_term {L : CoeffMatrix I} {i j : I} (h : L i j = 0) (x y : X) :
    L i j * G.d i x y = 0 := by
  rw [h, zero_mul]

/-- `d_i(x,y) = ∞` 时零系数项仍为零。 -/
theorem zero_coeff_term_of_top {L : CoeffMatrix I} {i j : I} (h : L i j = 0) {x y : X}
    (_htop : G.d i x y = ⊤) : L i j * G.d i x y = 0 :=
  zero_coeff_term G h x y

/-- 零系数项可从输出求和中删去。 -/
theorem sum_eq_sum_erase_of_zero_coeff [DecidableEq I] {L : CoeffMatrix I} {i j : I} (h : L i j = 0) (x y : X) :
    ∑ k, L k j * G.d k x y = ∑ k ∈ Finset.univ.erase i, L k j * G.d k x y :=
  (Finset.sum_erase (f := fun k => L k j * G.d k x y) Finset.univ
    (zero_coeff_term G h x y)).symm

/-- 证书形式：`L_{i→j} = 0` 时 `d_i` 项不参与 `d_j` 的输出上界。 -/
theorem lip_bound_without_zero_term [DecidableEq I] {φ : Operator X bot} {U : Set X} {L : CoeffMatrix I}
    (hL : L ∈ lipSetOn G φ U) {i j : I} (h : L i j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      G.d j (φ.func x) (φ.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * G.d k x y := by
  intro x hx y hy
  rw [← sum_eq_sum_erase_of_zero_coeff G h]
  exact hL.2 x hx y hy j

/-- 单行化简：`∀ k ≠ i, L_{k→j} = 0` 时 `d_j(φx,φy) ≤ L_{i→j} d_i(x,y)`（`i` 不必等于 `j`）。 -/
theorem lip_rowSparse_bound {φ : Operator X bot} {U : Set X} {L : CoeffMatrix I}
    (hL : L ∈ lipSetOn G φ U) {i j : I} (hrow : RowSparse L i j) :
    ∀ x ∈ U, ∀ y ∈ U, G.d j (φ.func x) (φ.func y) ≤ L i j * G.d i x y := by
  intro x hx y hy
  have h := hL.2 x hx y hy j
  rwa [Finset.sum_eq_single i (fun k _ hk => by rw [hrow k hk, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h)] at h

/-- 单通道常数与矩阵条目的关系（二者不等同）：行稀疏证书的条目 `L_{i→j}` 是可行常数，
故 `L̲_{i→j} ≤ L_{i→j}`。 -/
theorem channelLip_le_of_rowSparse {φ : Operator X bot} {U : Set X} {L : CoeffMatrix I}
    (hL : L ∈ lipSetOn G φ U) {i j : I} (hrow : RowSparse L i j) :
    L i j ∈ scalarFeasible G φ U i j ∧ channelLip G φ U i j ≤ L i j :=
  ⟨lip_rowSparse_bound G hL hrow, sInf_le (lip_rowSparse_bound G hL hrow)⟩

/-- 行解耦给出单输入分量上界。 -/
theorem RowDecoupled.bound {φ : Operator X bot} {U : Set X} {j : I}
    (h : RowDecoupled G φ U j) :
    ∃ L ∈ lipSetOn G φ U, ∃ i, ∀ x ∈ U, ∀ y ∈ U,
      G.d j (φ.func x) (φ.func y) ≤ L i j * G.d i x y := by
  obtain ⟨L, hL, i, hrow⟩ := h
  exact ⟨L, hL, i, lip_rowSparse_bound G hL hrow⟩

/-- 单列支撑：`∀ k ≠ j, L_{i→k} d_i(x,y) = 0`。 -/
theorem colSparse_term_eq_zero {L : CoeffMatrix I} {i j : I} (hcol : ColSparse L i j) :
    ∀ k, k ≠ j → ∀ x y : X, L i k * G.d i x y = 0 :=
  fun k hk x y => zero_coeff_term G (hcol k hk) x y

/-- 单列支撑的证书含义：对 `k ≠ j`，输出 `d_k` 的上界中不出现输入 `d_i`。 -/
theorem lip_colSparse_bound [DecidableEq I] {φ : Operator X bot} {U : Set X} {L : CoeffMatrix I}
    (hL : L ∈ lipSetOn G φ U) {i j : I} (hcol : ColSparse L i j) :
    ∀ k, k ≠ j → ∀ x ∈ U, ∀ y ∈ U,
      G.d k (φ.func x) (φ.func y) ≤ ∑ l ∈ Finset.univ.erase i, L l k * G.d l x y :=
  fun k hk => lip_bound_without_zero_term G hL (hcol k hk)

/-- 列解耦给出的贡献范围。 -/
theorem ColDecoupled.contribution {φ : Operator X bot} {U : Set X} {i : I}
    (h : ColDecoupled G φ U i) :
    ∃ L ∈ lipSetOn G φ U, ∃ j, ∀ k, k ≠ j → ∀ x y : X, L i k * G.d i x y = 0 := by
  obtain ⟨L, hL, j, hcol⟩ := h
  exact ⟨L, hL, j, colSparse_term_eq_zero G hcol⟩

/-- 完全解耦体系：对角证书给出逐分量标量上界。 -/
theorem lip_diagonal_bound {φ : Operator X bot} {U : Set X} {L : CoeffMatrix I}
    (hL : L ∈ lipSetOn G φ U) (hdiag : IsDiagonal L) :
    ∀ j, ∀ x ∈ U, ∀ y ∈ U, G.d j (φ.func x) (φ.func y) ≤ L j j * G.d j x y :=
  fun j => lip_rowSparse_bound G hL ((isDiagonal_iff_rowSparse L).mp hdiag j)

/-- 引理 h-6a98a58b5bc95360：只需 Lip 第 `j` 行对角稀疏即得标量双侧界。 -/
theorem two_sided_scalar_bound {φ : Operator X bot} {U : Set X} {L K : CoeffMatrix I}
    (hL : L ∈ lipSetOn G φ U) (hK : K ∈ coLipSetOn G φ U) {j : I}
    (hrow : ∀ k, k ≠ j → L k j = 0) :
    ∀ x ∈ U, ∀ y ∈ U,
      K j j * G.d j x y ≤ G.d j (φ.func x) (φ.func y) ∧
        G.d j (φ.func x) (φ.func y) ≤ L j j * G.d j x y :=
  fun x hx y hy => ⟨coLip_single_term_le G hK j j hx hy, lip_rowSparse_bound G hL hrow x hx y hy⟩

/-- 对所有 `j` 成立时的逐分量双侧界。 -/
theorem two_sided_scalar_bound_all {φ : Operator X bot} {U : Set X} {L K : CoeffMatrix I}
    (hL : L ∈ lipSetOn G φ U) (hK : K ∈ coLipSetOn G φ U)
    (hrow : ∀ j k, k ≠ j → L k j = 0) :
    ∀ j, ∀ x ∈ U, ∀ y ∈ U,
      K j j * G.d j x y ≤ G.d j (φ.func x) (φ.func y) ∧
        G.d j (φ.func x) (φ.func y) ≤ L j j * G.d j x y :=
  fun j => two_sided_scalar_bound G hL hK (hrow j)

/-- 另有 `L_{jj}, K_{jj} < ∞` 时得到有限标量双侧放缩界（系数取于 `ℝ≥0`）。 -/
theorem two_sided_scalar_bound_finite {φ : Operator X bot} {U : Set X} {L K : CoeffMatrix I}
    (hL : L ∈ lipSetOn G φ U) (hK : K ∈ coLipSetOn G φ U)
    (hrow : ∀ j k, k ≠ j → L k j = 0) (hfin : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    ∃ c C : I → NNReal, (∀ j, (c j : ENNReal) = K j j ∧ (C j : ENNReal) = L j j) ∧
      ∀ j, ∀ x ∈ U, ∀ y ∈ U,
        (c j : ENNReal) * G.d j x y ≤ G.d j (φ.func x) (φ.func y) ∧
          G.d j (φ.func x) (φ.func y) ≤ (C j : ENNReal) * G.d j x y := by
  refine ⟨fun j => (K j j).toNNReal, fun j => (L j j).toNNReal, fun j =>
    ⟨ENNReal.coe_toNNReal (hfin j).2.ne, ENNReal.coe_toNNReal (hfin j).1.ne⟩, ?_⟩
  intro j x hx y hy
  rw [ENNReal.coe_toNNReal (hfin j).2.ne, ENNReal.coe_toNNReal (hfin j).1.ne]
  exact two_sided_scalar_bound_all G hL hK hrow j x hx y hy

/-! ### 命题 h-f82672ec0dd48f28：正 co-Lip 通道的可分辨保持 -/

/-- (i) `K_{i→j} > 0` 时 `d_i(x,y) > 0 → d_j(φx,φy) > 0`。 -/
theorem coLip_pos_channel_preserves {φ : Operator X bot} {U : Set X} {K : CoeffMatrix I}
    (hK : K ∈ coLipSetOn G φ U) {i j : I} (hpos : 0 < K i j) :
    ∀ x ∈ U, ∀ y ∈ U, 0 < G.d i x y → 0 < G.d j (φ.func x) (φ.func y) := by
  intro x hx y hy hd
  exact (ENNReal.mul_pos hpos.ne' hd.ne').trans_le (coLip_single_term_le G hK i j hx hy)

/-- (ii) 对角 co-Lip 条目全正时 `φ` 反射族零距关系。 -/
theorem coLip_pos_diag_reflects {φ : Operator X bot} {U : Set X} {K : CoeffMatrix I}
    (hK : K ∈ coLipSetOn G φ U) (hpos : ∀ j, 0 < K j j) :
    ∀ x ∈ U, ∀ y ∈ U,
      GaugeZeroRelated G.d (φ.func x) (φ.func y) → GaugeZeroRelated G.d x y := by
  intro x hx y hy h j
  by_contra hne
  have := coLip_pos_channel_preserves G hK (hpos j) x hx y hy (pos_iff_ne_zero.mpr hne)
  exact this.ne' (h j)

end ChannelBounds

/-! ### 反例：零下确界未必由 `λ = 0` 实现 -/

section Counterexample

/-- 离散扩展度量：同点距离 `0`，异点距离 `∞`。 -/
def discreteDist (p q : Option Bool) : ENNReal := if p = q then 0 else ⊤

/-- `discreteDist` 满足扩展伪度量四公理（吸收元 `none`）。 -/
instance discreteDist_metric : ExtendedPseudoMetric (Option Bool) none discreteDist where
  nonabsorbing := ⟨some true, by simp⟩
  dist_self := fun x => by simp [discreteDist]
  symm := fun x y => by
    unfold discreteDist
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
  triangle := fun x y z => by
    unfold discreteDist
    by_cases hxz : x = z
    · simp [hxz]
    · by_cases hxy : x = y
      · subst hxy
        simp [hxz]
      · simp [hxy]
  isolate_bot := fun x hx => by simp [discreteDist, hx]

/-- 反例规范空间：`𝒳 = Option Bool`，`⊥ = none`，单分量 `I = Unit`。 -/
def exampleGauge : GaugeSpace (Option Bool) none Unit where
  d := fun _ => discreteDist
  metric := fun _ => discreteDist_metric

/-- 反例评估域 `U = dom(id) = {some true, some false}`。 -/
def exampleDomain : Set (Option Bool) := dom (opId : Operator (Option Bool) none)

theorem exampleDomain_nonempty : exampleDomain.Nonempty := ⟨some true, by simp [exampleDomain, mem_dom_iff]⟩

/-- 反例中每个正常数（含 `∞`）都可行。 -/
theorem example_pos_feasible :
    ∀ c : ENNReal, 0 < c → c ∈ scalarFeasible exampleGauge opId exampleDomain () () := by
  intro c hc x _ y _
  simp only [exampleGauge, opId_func, discreteDist]
  by_cases hxy : x = y
  · simp [hxy]
  · simp [hxy, ENNReal.mul_top hc.ne']

/-- 反例中 `λ = 0` 不可行。 -/
theorem example_zero_not_feasible :
    (0 : ENNReal) ∉ scalarFeasible exampleGauge opId exampleDomain () () := by
  intro h
  have h1 := h (some true) (by simp [exampleDomain, mem_dom_iff]) (some false)
    (by simp [exampleDomain, mem_dom_iff])
  simp [exampleGauge, discreteDist] at h1

/-- 反例中单通道 Lip 常数为 `0`。 -/
theorem example_channelLip_eq_zero : channelLip exampleGauge opId exampleDomain () () = 0 := by
  apply le_antisymm _ (zero_le _)
  by_contra h
  push Not at h
  obtain ⟨b, hb0, hb⟩ := exists_between h
  exact (not_le.mpr hb) (sInf_le (example_pos_feasible b hb0))

/-- 存在合法扩展规范空间、合法算子与非空合法评估域，使 `L̲_{i→j} = 0` 但 `0 ∉ S_{ij}`。 -/
theorem exists_channelLip_zero_not_attained :
    ∃ (X : Type) (bot : X) (I : Type) (_ : Fintype I) (_ : Nonempty I) (G : GaugeSpace X bot I)
      (φ : Operator X bot) (U : Set X) (i j : I),
      U.Nonempty ∧ U ⊆ dom φ ∧ channelLip G φ U i j = 0 ∧ (0 : ENNReal) ∉ scalarFeasible G φ U i j :=
  ⟨Option Bool, none, Unit, inferInstance, inferInstance, exampleGauge, opId, exampleDomain, (), (),
    exampleDomain_nonempty, subset_rfl, example_channelLip_eq_zero, example_zero_not_feasible⟩

end Counterexample

end formal_oet.vol_01.ch_02_operator_bounds

end
