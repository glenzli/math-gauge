# 第 2 章：完整 Lean 形式化

已完成冻结清单中的全部 40 项义务。下面给出全部目标源码、构建脚本和逐项对齐清单。

**来源与归属**：本形式化改写自附件中的 Zhe Li（Glen Li / glenzli），《The Operator Evolution Theory》第 2 章。作者 ORCID：https://orcid.org/0009-0006-6536-3453；官方作品页：https://glenzli.com/books/oet/；来源仓库：https://gitlab.com/glenzli/oet-public；许可：[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。本交付的改动是将冻结数学文本转写为 Lean 定义和内核核验的证明，部分证明使用等价的代数方法；不主张原理论为本回答独立发现。未检索上述网站或读取其他章节实现。

**核验**：使用题目提供的 Lean 4.29.1 与固定 mathlib 环境，运行 `sh build.sh` 成功，退出码为 0。`Main.lean` 导入全部目标模块，并逐个审计所有交付的具名定义与定理；公理依赖均限于 `propext`、`Classical.choice`、`Quot.sound`。没有新增公理、证明占位或绕过内核检查。

**表示约定**：
- 所有系数和距离使用 `ENNReal`，保留 `0·∞=0`。矩阵按输入、输出顺序存储，并证明与通常矩阵的转置显示及乘法相符。
- 列表按实际施行顺序存储。中间域是前缀复合的实际像；已证明逐步域合法性、最终像对应以及单步证书表示的等价性。链中不存储最终复合界。
- 全部路径是无约束的有限索引序列，不限于正路径；与通常 `Fin (n−1) → I` 序列有已证明的双射，并证明完整路径求和展开及单步边界。
- 不需要某些背景条件的定理证明了更强的一般形式，例如扰动界无需域合法性，路径判据对任意非空矩阵列表成立。在原文有限非空指标、扩展规范空间和合法作用域下直接专化即可。`Scalars` 在合法域上与原文公式完全相同，且定义自然延伸到任意集合；它不等同于矩阵条目的下确界。

构建入口为 `build.sh`，Lean 汇总入口为 `Main.lean`。以下六个 Lean 文件是全部新增目标源码。两份 `formal_oet/vol_01/ch_01_foundations/` 前置源码使用题目给定的冻结版本，未修改或覆盖；`lean-local` 使用题目提供的启动器。

```lean filename=Bounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ENNReal.Inv

open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations
namespace ChapterTwo
noncomputable section
variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
abbrev Mat (I : Type) := I → I → ENNReal
/-- Input first, output second. -/
def composeMat (B A : Mat I) : Mat I := fun i j => ∑ k, B k j * A i k
def display (A : Mat I) : Matrix I I ENNReal := fun j i => A i j
theorem display_compose (B A : Mat I) : display (composeMat B A) = display B * display A := rfl
def unitMat : Mat I := fun i j => if i = j then 1 else 0
theorem display_unit : display (unitMat : Mat I) = 1 := by
  ext i j
  simp [display, unitMat, Matrix.one_apply, eq_comm]
def act (A : Mat I) (v : I → ENNReal) (j : I) := ∑ i, A i j * v i
@[simp] theorem act_unit (v : I → ENNReal) (j : I) : act unitMat v j = v j := by
  simp [act, unitMat]
@[simp] theorem compose_unit (A : Mat I) : composeMat A unitMat = A := by
  ext i j
  simp [composeMat, unitMat]
@[simp] theorem unit_compose (A : Mat I) : composeMat unitMat A = A := by
  ext i j
  simp [composeMat, unitMat]
theorem act_compose (B A : Mat I) (v : I → ENNReal) (j : I) :
    act (composeMat B A) v j = act B (fun k => act A v k) j := by
  simp only [act, composeMat, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro i _
  exact mul_assoc _ _ _
theorem act_mono (A : Mat I) {v w : I → ENNReal} (h : ∀ i, v i ≤ w i) (j : I) :
    act A v j ≤ act A w j :=
  Finset.sum_le_sum (fun i _ => mul_le_mul_left' (h i) _)
def comp (g f : Operator X bot) : Operator X bot :=
  ⟨g.func ∘ f.func, by simp [f.preserves_bot, g.preserves_bot]⟩
def identity : Operator X bot := ⟨id, rfl⟩
def Lip (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set (Mat I) :=
  {A | U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
      d j (f.func x) (f.func y) ≤ act A (fun i => d i x y) j}
def GlobalLip (d : I → X → X → ENNReal) (f : Operator X bot) := Lip d f (dom f)
def CoLip (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) : Set (Mat I) :=
  {A | U.Nonempty ∧ U ⊆ dom f ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
      act A (fun i => d i x y) j ≤ d j (f.func x) (f.func y)}
variable {d : I → X → X → ENNReal} {f g : Operator X bot} {U V : Set X} {A B : Mat I}
theorem lip_restrict (h : A ∈ Lip d f V) (hUV : U ⊆ V) : A ∈ Lip d f U :=
  ⟨hUV.trans h.1, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩
theorem global_restrict (h : U ⊆ dom f) : GlobalLip d f ⊆ Lip d f U :=
  fun _ ha => lip_restrict ha h
noncomputable def entryInf (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) (i j : I) :=
  sInf ((fun A : Mat I => A i j) '' Lip d f U)
theorem entryInf_mono (h : U ⊆ V) (i j : I) : entryInf d f U i j ≤ entryInf d f V i j := by
  apply sInf_le_sInf
  rintro _ ⟨A, ha, rfl⟩
  exact ⟨A, lip_restrict ha h, rfl⟩
theorem singleton_lip [Subsingleton I] (h : A ∈ Lip d f U) (i : I)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i (f.func x) (f.func y) ≤ A i i * d i x y := by
  letI : Unique I := ⟨⟨i⟩, fun a => Subsingleton.elim a i⟩
  simpa [act] using h.2 x hx y hy i

theorem comp_dom (h : U ⊆ dom (comp g f)) : U ⊆ dom f := by
  intro x hx heq
  have hn := h hx
  apply hn
  change g.func (f.func x) = bot
  rw [heq, g.preserves_bot]
theorem comp_image_dom (h : U ⊆ dom (comp g f)) : f.func '' U ⊆ dom g := by
  rintro z ⟨x, hx, rfl⟩
  exact h hx

theorem lip_comp (hU : U ⊆ dom (comp g f)) (hA : A ∈ Lip d f U)
    (hB : B ∈ Lip d g (f.func '' U)) : composeMat B A ∈ Lip d (comp g f) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (g.func (f.func x)) (g.func (f.func y)) ≤ _
  rw [act_compose]
  exact (hB.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j).trans
    (act_mono B (fun k => hA.2 x hx y hy k) j)
theorem colip_comp (hU : U ⊆ dom (comp g f)) (hA : A ∈ CoLip d f U)
    (hB : B ∈ CoLip d g (f.func '' U)) : composeMat B A ∈ CoLip d (comp g f) U := by
  refine ⟨hA.1, hU, ?_⟩
  intro x hx y hy j
  rw [act_compose]
  exact (act_mono B (fun k => hA.2.2 x hx y hy k) j).trans
    (hB.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)
theorem colip_term (h : A ∈ CoLip d f U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    A i j * d i x y ≤ d j (f.func x) (f.func y) :=
  (Finset.single_le_sum (fun k _ => zero_le (A k j * d k x y)) (Finset.mem_univ i)).trans
    (h.2.2 x hx y hy j)
theorem colip_zero (h : A ∈ CoLip d f U) {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    {i j : I} (hout : d j (f.func x) (f.func y) = 0) (hin : 0 < d i x y) : A i j = 0 := by
  have hz : A i j * d i x y = 0 := le_antisymm (hout ▸ colip_term h hx hy i j) (zero_le _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hin)

theorem perturb_forward (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (f.func z) (g.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (g.func x) (g.func y) ≤ d j (f.func x) (f.func y) + δ j + δ j := by
  calc
    _ ≤ d j (g.func x) (f.func x) + d j (f.func x) (g.func y) := (hd j).triangle _ _ _
    _ ≤ d j (g.func x) (f.func x) + (d j (f.func x) (f.func y) + d j (f.func y) (g.func y)) :=
      add_le_add le_rfl ((hd j).triangle _ _ _)
    _ ≤ δ j + (d j (f.func x) (f.func y) + δ j) := by
      rw [(hd j).symm (g.func x) (f.func x)]
      exact add_le_add (hδ x hx j) (add_le_add le_rfl (hδ y hy j))
    _ = _ := by simp only [add_comm, add_left_comm, add_assoc]
theorem perturb_reverse (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (f.func z) (g.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (f.func x) (f.func y) ≤ d j (g.func x) (g.func y) + δ j + δ j := by
  apply perturb_forward hd (f := g) (g := f) _ hx hy j
  intro z hz k
  rw [(hd k).symm]
  exact hδ z hz k
theorem perturb_lip (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (f.func z) (g.func z) ≤ δ j)
    (h : A ∈ Lip d f U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (g.func x) (g.func y) ≤ act A (fun i => d i x y) j + 2 * δ j := by
  simpa [two_mul, add_assoc] using
    (perturb_forward hd hδ hx hy j).trans (add_le_add (add_le_add (h.2 x hx y hy j) le_rfl) le_rfl)
theorem perturb_colip (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (f.func z) (g.func z) ≤ δ j)
    (h : A ∈ CoLip d f U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    act A (fun i => d i x y) j ≤ d j (g.func x) (g.func y) + 2 * δ j := by
  simpa [two_mul, add_assoc] using (h.2.2 x hx y hy j).trans (perturb_reverse hd hδ hx hy j)

theorem identity_lip (h : U ⊆ dom (identity : Operator X bot)) : unitMat ∈ Lip d (identity : Operator X bot) U :=
  ⟨h, by intro x hx y hy j; simp [identity]⟩
theorem identity_colip (hU : U.Nonempty) (h : U ⊆ dom (identity : Operator X bot)) :
    unitMat ∈ CoLip d (identity : Operator X bot) U :=
  ⟨hU, h, by intro x hx y hy j; simp [identity]⟩

def Channel (I : Type) := I × I
def Row (A : Mat I) (i j : I) := ∀ k, k ≠ i → A k j = 0
def Col (A : Mat I) (i j : I) := ∀ k, k ≠ j → A i k = 0
def Diagonal (A : Mat I) := ∀ i j, i ≠ j → A i j = 0
def RowDecoupled (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) (j : I) :=
  ∃ A ∈ Lip d f U, ∃ i, Row A i j
def ColDecoupled (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) (i : I) :=
  ∃ A ∈ Lip d f U, ∃ j, Col A i j

theorem zero_term {i j : I} (h : A i j = 0) (v : I → ENNReal) : A i j * v i = 0 := by rw [h, zero_mul]
theorem delete_zero_term {i j : I} (h : A i j = 0) (v : I → ENNReal) :
    act A v j = ∑ k ∈ Finset.univ.erase i, A k j * v k := by
  have hh := Finset.sum_erase_add (s := Finset.univ) (f := fun k => A k j * v k) (Finset.mem_univ i)
  simpa [act, h] using hh.symm
theorem row_act {i j : I} (h : Row A i j) (v : I → ENNReal) : act A v j = A i j * v i := by
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [h k hki, zero_mul]
  · simp

theorem row_bound (h : A ∈ Lip d f U) {i j : I} (hr : Row A i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d j (f.func x) (f.func y) ≤ A i j * d i x y := by
  simpa [row_act hr] using h.2 x hx y hy j
theorem col_contribution {i j : I} (hc : Col A i j) {k : I} (hk : k ≠ j)
    (v : I → ENNReal) : A i k * v i = 0 := zero_term (hc k hk) v
theorem diagonal_bound (h : A ∈ Lip d f U) (hA : Diagonal A)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (f.func x) (f.func y) ≤ A j j * d j x y :=
  row_bound h (fun k hk => hA k j hk) hx hy

theorem two_sided (hA : A ∈ Lip d f U) (hB : B ∈ CoLip d f U)
    {j : I} (hr : Row A j j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    B j j * d j x y ≤ d j (f.func x) (f.func y) ∧
    d j (f.func x) (f.func y) ≤ A j j * d j x y :=
  ⟨colip_term hB hx hy j j, row_bound hA hr hx hy⟩
theorem all_two_sided (hA : A ∈ Lip d f U) (hB : B ∈ CoLip d f U)
    (hr : ∀ j, Row A j j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    ∀ j, B j j * d j x y ≤ d j (f.func x) (f.func y) ∧
      d j (f.func x) (f.func y) ≤ A j j * d j x y :=
  fun j => two_sided hA hB (hr j) hx hy
theorem finite_two_sided (hA : A ∈ Lip d f U) (hB : B ∈ CoLip d f U)
    (hr : ∀ j, Row A j j) (hfin : ∀ j, A j j < ⊤ ∧ B j j < ⊤)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    ∀ j, A j j < ⊤ ∧ B j j < ⊤ ∧
      B j j * d j x y ≤ d j (f.func x) (f.func y) ∧
      d j (f.func x) (f.func y) ≤ A j j * d j x y :=
  fun j => ⟨(hfin j).1, (hfin j).2, all_two_sided hA hB hr hx hy j⟩
theorem positive_channel (h : A ∈ CoLip d f U) {i j : I} (ha : 0 < A i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hin : 0 < d i x y) :
    0 < d j (f.func x) (f.func y) :=
  (ENNReal.mul_pos (ne_of_gt ha) (ne_of_gt hin)).trans_le (colip_term h hx hy i j)
theorem reflects_zero (h : A ∈ CoLip d f U) (ha : ∀ j, 0 < A j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hz : GaugeZeroRelated d (f.func x) (f.func y)) : GaugeZeroRelated d x y := by
  intro j
  by_contra hn
  have hp := positive_channel h (ha j) hx hy (pos_iff_ne_zero.mpr hn)
  rw [hz j] at hp
  exact (lt_irrefl 0) hp
end
end ChapterTwo
```

```lean filename=Chains.lean
import Bounds
open scoped BigOperators
open formal_oet.vol_01.ch_01_foundations
namespace ChapterTwo
noncomputable section
variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
/-- Lists are in execution order, first step at the head. -/
def chain : List (Operator X bot) → Operator X bot
  | [] => identity
  | f :: fs => comp (chain fs) f
def product : List (Mat I) → Mat I
  | [] => unitMat
  | A :: As => composeMat (product As) A
@[simp] theorem product_nil : product ([] : List (Mat I)) = unitMat := rfl
@[simp] theorem product_single (A : Mat I) : product [A] = A := unit_compose A
/-- The final actual image, computed without any bounds. -/
def images : List (Operator X bot) → Set X → Set X
  | [], U => U
  | f :: fs, U => images fs (f.func '' U)
theorem images_eq (fs : List (Operator X bot)) (U : Set X) : images fs U = (chain fs).func '' U := by
  induction fs generalizing U with
  | nil => simp [images, chain, identity]
  | cons f fs ih => simp [images, ih, chain, comp, Set.image_image]
/-- Every step is defined on its actual input image. -/
def StepDomains : List (Operator X bot) → Set X → Prop
  | [], _ => True
  | f :: fs, U => U ⊆ dom f ∧ StepDomains fs (f.func '' U)
theorem step_domains (fs : List (Operator X bot)) (U : Set X) (h : U ⊆ dom (chain fs)) :
    StepDomains fs U := by
  induction fs generalizing U with
  | nil => trivial
  | cons f fs ih => exact ⟨comp_dom h, ih _ (comp_image_dom h)⟩
theorem stepDomains_iff_stages (fs : List (Operator X bot)) (U : Set X) :
    StepDomains fs U ↔ ∀ k : Fin fs.length,
      images (fs.take k.val) U ⊆ dom (fs.get k) := by
  induction fs generalizing U with
  | nil => simp [StepDomains]
  | cons f fs ih =>
    change StepDomains (f :: fs) U ↔ ∀ k : Fin (fs.length + 1),
      images ((f :: fs).take k.val) U ⊆ dom ((f :: fs).get k)
    rw [Fin.forall_fin_succ]
    simp [StepDomains, ih, images]
theorem chain_stage_domains (fs : List (Operator X bot)) (U : Set X)
    (h : U ⊆ dom (chain fs)) (k : Fin fs.length) :
    images (fs.take k.val) U ⊆ dom (fs.get k) :=
  (stepDomains_iff_stages fs U).mp (step_domains fs U h) k

/-- A step consists only of an operator and a selected coefficient matrix. -/
abbrev Step (X I : Type) (bot : X) := Operator X bot × Mat I
def StepLip (d : I → X → X → ENNReal) : List (Step X I bot) → Set X → Prop
  | [], _ => True
  | s :: ss, U => s.2 ∈ Lip d s.1 U ∧ StepLip d ss (s.1.func '' U)
def StepCoLip (d : I → X → X → ENNReal) : List (Step X I bot) → Set X → Prop
  | [], _ => True
  | s :: ss, U => s.2 ∈ CoLip d s.1 U ∧ StepCoLip d ss (s.1.func '' U)
/-- Converts separately supplied, chronological step data into the paired representation. -/
def packSteps (n : ℕ) (fs : Fin n → Operator X bot) (ms : Fin n → Mat I) : List (Step X I bot) :=
  List.ofFn (fun k => (fs k, ms k))
@[simp] theorem packSteps_ops (n : ℕ) (fs : Fin n → Operator X bot) (ms : Fin n → Mat I) :
    (packSteps n fs ms).map Prod.fst = List.ofFn fs := by simp [packSteps, List.map_ofFn, Function.comp_def]
@[simp] theorem packSteps_mats (n : ℕ) (fs : Fin n → Operator X bot) (ms : Fin n → Mat I) :
    (packSteps n fs ms).map Prod.snd = List.ofFn ms := by simp [packSteps, List.map_ofFn, Function.comp_def]

/-- Actual input at index k is the image under the preceding k operations. -/
def stage (ss : List (Step X I bot)) (U : Set X) (k : ℕ) : Set X :=
  images ((ss.take k).map Prod.fst) U

theorem stepLip_iff_stages (d : I → X → X → ENNReal)
    (ss : List (Step X I bot)) (U : Set X) :
    StepLip d ss U ↔ ∀ k : Fin ss.length,
      (ss.get k).2 ∈ Lip d (ss.get k).1 (stage ss U k.val) := by
  induction ss generalizing U with
  | nil => simp [StepLip]
  | cons s ss ih =>
    change StepLip d (s :: ss) U ↔ ∀ k : Fin (ss.length + 1),
      ((s :: ss).get k).2 ∈ Lip d ((s :: ss).get k).1 (stage (s :: ss) U k.val)
    rw [Fin.forall_fin_succ]
    simp [StepLip, ih, stage, List.get_cons_succ, images]

theorem stepCoLip_iff_stages (d : I → X → X → ENNReal)
    (ss : List (Step X I bot)) (U : Set X) :
    StepCoLip d ss U ↔ ∀ k : Fin ss.length,
      (ss.get k).2 ∈ CoLip d (ss.get k).1 (stage ss U k.val) := by
  induction ss generalizing U with
  | nil => simp [StepCoLip]
  | cons s ss ih =>
    change StepCoLip d (s :: ss) U ↔ ∀ k : Fin (ss.length + 1),
      ((s :: ss).get k).2 ∈ CoLip d ((s :: ss).get k).1 (stage (s :: ss) U k.val)
    rw [Fin.forall_fin_succ]
    simp [StepCoLip, ih, stage, List.get_cons_succ, images]

theorem chain_lip (d : I → X → X → ENNReal) (ss : List (Step X I bot)) (U : Set X)
    (hdom : U ⊆ dom (chain (ss.map Prod.fst))) (h : StepLip d ss U) :
    product (ss.map Prod.snd) ∈ Lip d (chain (ss.map Prod.fst)) U := by
  induction ss generalizing U with
  | nil => exact identity_lip hdom
  | cons s ss ih =>
    exact lip_comp hdom h.1 (ih _ (comp_image_dom hdom) h.2)
theorem chain_colip (d : I → X → X → ENNReal) (ss : List (Step X I bot)) (U : Set X)
    (hne : U.Nonempty) (hdom : U ⊆ dom (chain (ss.map Prod.fst))) (h : StepCoLip d ss U) :
    product (ss.map Prod.snd) ∈ CoLip d (chain (ss.map Prod.fst)) U := by
  induction ss generalizing U with
  | nil => exact identity_colip hne hdom
  | cons s ss ih =>
    exact colip_comp hdom h.1 (ih _ (hne.image s.1.func) (comp_image_dom hdom) h.2)
theorem chain_colip_positive_length (d : I → X → X → ENNReal)
    (s : Step X I bot) (ss : List (Step X I bot)) (U : Set X)
    (hdom : U ⊆ dom (chain ((s :: ss).map Prod.fst))) (h : StepCoLip d (s :: ss) U) :
    product ((s :: ss).map Prod.snd) ∈ CoLip d (chain ((s :: ss).map Prod.fst)) U :=
  chain_colip d (s :: ss) U h.1.1 hdom h
/-- The original individually indexed hypotheses construct the recursive proof data. -/
theorem chain_lip_stages (d : I → X → X → ENNReal) (ss : List (Step X I bot)) (U : Set X)
    (hdom : U ⊆ dom (chain (ss.map Prod.fst)))
    (h : ∀ k : Fin ss.length, (ss.get k).2 ∈ Lip d (ss.get k).1 (stage ss U k.val)) :
    product (ss.map Prod.snd) ∈ Lip d (chain (ss.map Prod.fst)) U :=
  chain_lip d ss U hdom ((stepLip_iff_stages d ss U).mpr h)
theorem chain_colip_stages (d : I → X → X → ENNReal)
    (s : Step X I bot) (ss : List (Step X I bot)) (U : Set X)
    (hdom : U ⊆ dom (chain ((s :: ss).map Prod.fst)))
    (h : ∀ k : Fin (s :: ss).length,
      ((s :: ss).get k).2 ∈ CoLip d ((s :: ss).get k).1 (stage (s :: ss) U k.val)) :
    product ((s :: ss).map Prod.snd) ∈ CoLip d (chain ((s :: ss).map Prod.fst)) U :=
  chain_colip_positive_length d s ss U hdom ((stepCoLip_iff_stages d (s :: ss) U).mpr h)
end
end ChapterTwo
```

```lean filename=Paths.lean
import Chains
import Mathlib.Data.Fin.Tuple.Basic
open scoped BigOperators
namespace ChapterTwo
noncomputable section
variable {I : Type} [Fintype I] [DecidableEq I]
/-- Exactly n unrestricted intermediate indices, not just positive paths. -/
def Route (I : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => I × Route I n
/-- Bijection to the ordinary full finite index sequence. -/
def routeEquiv (I : Type) : (n : ℕ) → Route I n ≃ (Fin n → I)
  | 0 => { toFun := fun _ => Fin.elim0, invFun := fun _ => (),
           left_inv := fun x => by cases x; rfl,
           right_inv := fun f => by funext k; exact Fin.elim0 k }
  | n + 1 => (Equiv.prodCongr (Equiv.refl I) (routeEquiv I n)).trans (Fin.consEquiv (fun _ => I))
instance routeFintype : (n : ℕ) → Fintype (Route I n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => letI := routeFintype n; inferInstanceAs (Fintype (I × Route I n))

def routeWeight (A : Mat I) : (As : List (Mat I)) → I → I → Route I As.length → ENNReal
  | [], i, j, _ => A i j
  | B :: Bs, i, j, p => A i p.1 * routeWeight B Bs p.1 j p.2
def AllPositive (A : Mat I) : (As : List (Mat I)) → I → I → Route I As.length → Prop
  | [], i, j, _ => 0 < A i j
  | B :: Bs, i, j, p => 0 < A i p.1 ∧ AllPositive B Bs p.1 j p.2
def HasZero (A : Mat I) : (As : List (Mat I)) → I → I → Route I As.length → Prop
  | [], i, j, _ => A i j = 0
  | B :: Bs, i, j, p => A i p.1 = 0 ∨ HasZero B Bs p.1 j p.2

theorem weight_zero_iff (A : Mat I) (As : List (Mat I)) (i j : I) (p : Route I As.length) :
    routeWeight A As i j p = 0 ↔ HasZero A As i j p := by
  induction As generalizing A i with
  | nil => rfl
  | cons B Bs ih => simp only [routeWeight, HasZero, mul_eq_zero, ih]
theorem weight_positive_iff (A : Mat I) (As : List (Mat I)) (i j : I) (p : Route I As.length) :
    0 < routeWeight A As i j p ↔ AllPositive A As i j p := by
  induction As generalizing A i with
  | nil => rfl
  | cons B Bs ih => simp only [routeWeight, AllPositive, ENNReal.mul_pos_iff, ih]

/-- Explicit expansion over all n-1 intermediate index sequences. -/
theorem product_path_sum (A : Mat I) (As : List (Mat I)) (i j : I) :
    product (A :: As) i j = ∑ p : Route I As.length, routeWeight A As i j p := by
  induction As generalizing A i with
  | nil => simp [product_single, routeWeight, Route]
  | cons B Bs ih =>
    change (∑ k, product (B :: Bs) k j * A i k) =
      ∑ p : I × Route I Bs.length, A i p.1 * routeWeight B Bs p.1 j p.2
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k _
    rw [ih B k, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    exact mul_comm _ _

/-- Zero criterion for all coefficient lists, hence also all selected Lip certificates. -/
theorem product_zero_iff (A : Mat I) (As : List (Mat I)) (i j : I) :
    product (A :: As) i j = 0 ↔ ∀ p : Route I As.length, HasZero A As i j p := by
  induction As generalizing A i with
  | nil => simp [product_single, HasZero, Route]
  | cons B Bs ih =>
    change (∑ k, product (B :: Bs) k j * A i k) = 0 ↔ _
    rw [Finset.sum_eq_zero_iff]
    constructor
    · intro h p
      rcases mul_eq_zero.mp (h p.1 (Finset.mem_univ _)) with ht | ha
      · exact Or.inr ((ih B p.1).mp ht p.2)
      · exact Or.inl ha
    · intro h k _
      by_cases ha : A i k = 0
      · simp [ha]
      · have ht : product (B :: Bs) k j = 0 := (ih B k).mpr (fun p => (h (k, p)).resolve_left ha)
        simp [ht]
/-- Positive criterion for all coefficient lists, hence also all selected co-Lip certificates. -/
theorem product_positive_iff (A : Mat I) (As : List (Mat I)) (i j : I) :
    0 < product (A :: As) i j ↔ ∃ p : Route I As.length, AllPositive A As i j p := by
  induction As generalizing A i with
  | nil => simp [product_single, AllPositive, Route]
  | cons B Bs ih =>
    change 0 < (∑ k, product (B :: Bs) k j * A i k) ↔ _
    rw [Finset.sum_pos_iff]
    constructor
    · rintro ⟨k, _, hk⟩
      obtain ⟨ht, ha⟩ := ENNReal.mul_pos_iff.mp hk
      obtain ⟨p, hp⟩ := (ih B k).mp ht
      exact ⟨(k, p), ha, hp⟩
    · rintro ⟨p, hp⟩
      exact ⟨p.1, Finset.mem_univ _, ENNReal.mul_pos_iff.mpr ⟨(ih B p.1).mpr ⟨p.2, hp.2⟩, hp.1⟩⟩

/-- The explicit n=1 boundary contains exactly the empty sequence. -/
theorem one_step_paths (A : Mat I) (i j : I) :
    (∀ p : Route I 0, HasZero A [] i j p) ↔ A i j = 0 := by simp [HasZero, Route]
theorem one_step_positive (A : Mat I) (i j : I) :
    (∃ p : Route I 0, AllPositive A [] i j p) ↔ 0 < A i j := by simp [AllPositive, Route]
end
end ChapterTwo
```

```lean filename=Scalar.lean
import Bounds
open formal_oet.vol_01.ch_01_foundations
namespace ChapterTwo
noncomputable section
variable {X I : Type} {bot : X}
/-- No coefficient matrix is involved in this single-channel feasible set. -/
def Scalars (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) (i j : I) : Set ENNReal :=
  {a | ∀ x ∈ U, ∀ y ∈ U, d j (f.func x) (f.func y) ≤ a * d i x y}
def scalarInf (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf (Scalars d f U i j)
variable {d : I → X → X → ENNReal} {f : Operator X bot} {U : Set X} {i j : I}
theorem scalars_upward {a b : ENNReal} (ha : a ∈ Scalars d f U i j) (hab : a ≤ b) :
    b ∈ Scalars d f U i j := by
  intro x hx y hy
  exact (ha x hx y hy).trans (mul_le_mul_right' hab _)
theorem above_inf_feasible {a : ENNReal} (h : scalarInf d f U i j < a) :
    a ∈ Scalars d f U i j := by
  obtain ⟨b, hb, hba⟩ := sInf_lt_iff.mp h
  exact scalars_upward hb hba.le
theorem zero_inf_positive {a : ENNReal} (h : scalarInf d f U i j = 0) (ha : 0 < a) :
    a ∈ Scalars d f U i j := above_inf_feasible (h ▸ ha)
theorem finite_inf_iff : scalarInf d f U i j < ⊤ ↔
    ∃ a : ENNReal, a < ⊤ ∧ a ∈ Scalars d f U i j := by
  change sInf (Scalars d f U i j) < ⊤ ↔ _
  rw [sInf_lt_iff]
  exact exists_congr (fun _ => and_comm)
theorem impossible_channel {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (f.func x) (f.func y)) :
    Scalars d f U i j = ∅ ∧ scalarInf d f U i j = ⊤ := by
  have he : Scalars d f U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hh := ha x hx y hy
    rw [hin, mul_zero] at hh
    exact (not_le_of_gt hout) hh
  exact ⟨he, by simp [scalarInf, he]⟩
theorem positive_finite_inf_attained (hpos : 0 < scalarInf d f U i j)
    (hfin : scalarInf d f U i j < ⊤) :
    scalarInf d f U i j ∈ Scalars d f U i j := by
  intro x hx y hy
  by_cases hz : d i x y = 0
  · obtain ⟨a, _, ha⟩ := finite_inf_iff.mp hfin
    simpa [hz] using ha x hx y hy
  by_cases ht : d i x y = ⊤
  · simp [ht, ENNReal.mul_top (ne_of_gt hpos)]
  · apply (ENNReal.div_le_iff hz ht).mp
    apply le_sInf
    intro a ha
    exact (ENNReal.div_le_iff hz ht).mpr (ha x hx y hy)
end
end ChapterTwo
```

```lean filename=Counterexample.lean
import Scalar
namespace ChapterTwo
open formal_oet.vol_01.ch_01_foundations
noncomputable section
/-- Two ordinary points and a distinct absorbing point. -/
abbrev CounterX := Option Bool
def counterDist (i : Bool) (x y : CounterX) : ENNReal :=
  if x = y then 0 else if x = none ∨ y = none then ⊤ else if i then 1 else ⊤
theorem counterMetric (i : Bool) : ExtendedPseudoMetric CounterX none (counterDist i) where
  nonabsorbing := ⟨some false, by simp⟩
  dist_self := by intro x; simp [counterDist]
  symm := by
    intro x y
    fin_cases i <;> fin_cases x <;> fin_cases y <;> simp [counterDist]
  triangle := by
    intro x y z
    fin_cases i <;> fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [counterDist, Option.some_ne_none, eq_comm]
  isolate_bot := by intro x hx; simp [counterDist, hx]
def counterOp : Operator CounterX none := identity
def counterDomain : Set CounterX := {x | x ≠ none}
theorem counterDomain_nonempty : counterDomain.Nonempty := ⟨some false, by simp [counterDomain]⟩
theorem counterDomain_legal : counterDomain ⊆ dom counterOp := by
  intro x hx; exact hx

theorem counter_positive_feasible {a : ENNReal} (ha : 0 < a) :
    a ∈ Scalars counterDist counterOp counterDomain false true := by
  intro x hx y hy
  have hx' : x ≠ none := hx
  have hy' : y ≠ none := hy
  change counterDist true x y ≤ a * counterDist false x y
  by_cases hxy : x = y
  · simp [counterDist, hxy]
  · simp [counterDist, hxy, hx', hy', ENNReal.mul_top (ne_of_gt ha)]
theorem counter_zero_infeasible :
    0 ∉ Scalars counterDist counterOp counterDomain false true := by
  intro h
  have hh := h (some false) (by simp [counterDomain]) (some true) (by simp [counterDomain])
  simp [counterOp, identity, counterDist, Option.some_ne_none] at hh
theorem counter_inf_zero : scalarInf counterDist counterOp counterDomain false true = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_forall_gt
  intro a ha
  obtain ⟨b, hb, hba⟩ := exists_between ha
  exact (sInf_le (counter_positive_feasible hb)).trans_lt hba
theorem zero_inf_not_attained_example :
    (∀ i, ExtendedPseudoMetric CounterX none (counterDist i)) ∧
    counterDomain.Nonempty ∧ counterDomain ⊆ dom counterOp ∧
    scalarInf counterDist counterOp counterDomain false true = 0 ∧
    0 ∉ Scalars counterDist counterOp counterDomain false true :=
  ⟨counterMetric, counterDomain_nonempty, counterDomain_legal, counter_inf_zero, counter_zero_infeasible⟩
end
end ChapterTwo
```

```lean filename=Main.lean
import Bounds
import Chains
import Paths
import Scalar
import Counterexample

/- Kernel axiom audit for every delivered named definition and theorem. -/
#print axioms ChapterTwo.Mat
#print axioms ChapterTwo.composeMat
#print axioms ChapterTwo.display
#print axioms ChapterTwo.display_compose
#print axioms ChapterTwo.unitMat
#print axioms ChapterTwo.display_unit
#print axioms ChapterTwo.act
#print axioms ChapterTwo.act_unit
#print axioms ChapterTwo.compose_unit
#print axioms ChapterTwo.unit_compose
#print axioms ChapterTwo.act_compose
#print axioms ChapterTwo.act_mono
#print axioms ChapterTwo.comp
#print axioms ChapterTwo.identity
#print axioms ChapterTwo.Lip
#print axioms ChapterTwo.GlobalLip
#print axioms ChapterTwo.CoLip
#print axioms ChapterTwo.lip_restrict
#print axioms ChapterTwo.global_restrict
#print axioms ChapterTwo.entryInf
#print axioms ChapterTwo.entryInf_mono
#print axioms ChapterTwo.singleton_lip
#print axioms ChapterTwo.comp_dom
#print axioms ChapterTwo.comp_image_dom
#print axioms ChapterTwo.lip_comp
#print axioms ChapterTwo.colip_comp
#print axioms ChapterTwo.colip_term
#print axioms ChapterTwo.colip_zero
#print axioms ChapterTwo.perturb_forward
#print axioms ChapterTwo.perturb_reverse
#print axioms ChapterTwo.perturb_lip
#print axioms ChapterTwo.perturb_colip
#print axioms ChapterTwo.identity_lip
#print axioms ChapterTwo.identity_colip
#print axioms ChapterTwo.Channel
#print axioms ChapterTwo.Row
#print axioms ChapterTwo.Col
#print axioms ChapterTwo.Diagonal
#print axioms ChapterTwo.RowDecoupled
#print axioms ChapterTwo.ColDecoupled
#print axioms ChapterTwo.zero_term
#print axioms ChapterTwo.delete_zero_term
#print axioms ChapterTwo.row_act
#print axioms ChapterTwo.row_bound
#print axioms ChapterTwo.col_contribution
#print axioms ChapterTwo.diagonal_bound
#print axioms ChapterTwo.two_sided
#print axioms ChapterTwo.all_two_sided
#print axioms ChapterTwo.finite_two_sided
#print axioms ChapterTwo.positive_channel
#print axioms ChapterTwo.reflects_zero
#print axioms ChapterTwo.chain
#print axioms ChapterTwo.product
#print axioms ChapterTwo.product_nil
#print axioms ChapterTwo.product_single
#print axioms ChapterTwo.images
#print axioms ChapterTwo.images_eq
#print axioms ChapterTwo.StepDomains
#print axioms ChapterTwo.step_domains
#print axioms ChapterTwo.stepDomains_iff_stages
#print axioms ChapterTwo.chain_stage_domains
#print axioms ChapterTwo.Step
#print axioms ChapterTwo.StepLip
#print axioms ChapterTwo.StepCoLip
#print axioms ChapterTwo.packSteps
#print axioms ChapterTwo.packSteps_ops
#print axioms ChapterTwo.packSteps_mats
#print axioms ChapterTwo.stage
#print axioms ChapterTwo.stepLip_iff_stages
#print axioms ChapterTwo.stepCoLip_iff_stages
#print axioms ChapterTwo.chain_lip
#print axioms ChapterTwo.chain_colip
#print axioms ChapterTwo.chain_colip_positive_length
#print axioms ChapterTwo.chain_lip_stages
#print axioms ChapterTwo.chain_colip_stages
#print axioms ChapterTwo.Route
#print axioms ChapterTwo.routeEquiv
#print axioms ChapterTwo.routeFintype
#print axioms ChapterTwo.routeWeight
#print axioms ChapterTwo.AllPositive
#print axioms ChapterTwo.HasZero
#print axioms ChapterTwo.weight_zero_iff
#print axioms ChapterTwo.weight_positive_iff
#print axioms ChapterTwo.product_path_sum
#print axioms ChapterTwo.product_zero_iff
#print axioms ChapterTwo.product_positive_iff
#print axioms ChapterTwo.one_step_paths
#print axioms ChapterTwo.one_step_positive
#print axioms ChapterTwo.Scalars
#print axioms ChapterTwo.scalarInf
#print axioms ChapterTwo.scalars_upward
#print axioms ChapterTwo.above_inf_feasible
#print axioms ChapterTwo.zero_inf_positive
#print axioms ChapterTwo.finite_inf_iff
#print axioms ChapterTwo.impossible_channel
#print axioms ChapterTwo.positive_finite_inf_attained
#print axioms ChapterTwo.CounterX
#print axioms ChapterTwo.counterDist
#print axioms ChapterTwo.counterMetric
#print axioms ChapterTwo.counterOp
#print axioms ChapterTwo.counterDomain
#print axioms ChapterTwo.counterDomain_nonempty
#print axioms ChapterTwo.counterDomain_legal
#print axioms ChapterTwo.counter_positive_feasible
#print axioms ChapterTwo.counter_zero_infeasible
#print axioms ChapterTwo.counter_inf_zero
#print axioms ChapterTwo.zero_inf_not_attained_example
```

```sh filename=build.sh
#!/bin/sh
set -eu
# lean-local is the supplied Lean 4.29.1 / pinned-mathlib launcher.
./lean-local -o formal_oet/vol_01/ch_01_foundations/gauge_space.olean formal_oet/vol_01/ch_01_foundations/gauge_space.lean
./lean-local -o formal_oet/vol_01/ch_01_foundations/operator_space.olean formal_oet/vol_01/ch_01_foundations/operator_space.lean
for module in Bounds Chains Paths Scalar Counterexample Main; do
  ./lean-local -o "$module.olean" "$module.lean"
done
```

```json filename=alignment.json
{
  "case_id": "HCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "HC02-D01",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.Lip"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.GlobalLip"
        }
      ],
      "representation": "Lip 的成员条件同时包含 U⊆dom φ 与全部 x,y∈U、输出 j 的求和上界；GlobalLip 取 U=dom φ。矩阵系数和距离均为 ENNReal。Fintype 表示有限指标，原文非空指标是这些更一般声明的特例。",
      "dependencies": []
    },
    {
      "id": "HC02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.CoLip"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.colip_term"
        }
      ],
      "representation": "CoLip 的成员条件明确包含 U.Nonempty、U⊆dom φ 和全部点对/输出分量的求和下界。colip_term 从有限非负和中抽取任意通道项，不是额外假设。",
      "dependencies": []
    },
    {
      "id": "HC02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.Mat"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.composeMat"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.display"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.display_compose"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.act"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.act_compose"
        }
      ],
      "representation": "Mat i j 输入优先；display M 的通常第 j 行第 i 列是 M i j。display_compose 证明所用 Σk B k j*A i k 与通常矩阵 B*A 一致，act_compose 证明对距离向量的复合等式。",
      "dependencies": []
    },
    {
      "id": "HC02-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.chain"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.product"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.product_nil"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.product_single"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.unitMat"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.display_unit"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.compose_unit"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.unit_compose"
        }
      ],
      "representation": "列表按施行顺序存储。chain(f::fs)=chain(fs)∘f；product(A::As)=product(As)*A。空表分别为恒等算子和单位矩阵，单元素乘积等于其矩阵。Bounds.unitMat 明确定义 Kronecker δ，display_unit 证明它是通常单位矩阵。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.images"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.images_eq"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.StepDomains"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.step_domains"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.stepDomains_iff_stages"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.chain_stage_domains"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.Step"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.StepLip"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.StepCoLip"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.packSteps"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.packSteps_ops"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.packSteps_mats"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.stage"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.stepLip_iff_stages"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.stepCoLip_iff_stages"
        }
      ],
      "representation": "images 逐步取实际像；images_eq 证明最终实际像等于完整复合像。由初始域包含于完整复合定义域，chain_stage_domains 给出每个前缀像包含于下一步定义域。Step 仅存算子和矩阵；StepLip/StepCoLip 仅记录实际域上的单步界。stage 与两个 iff 将递归表示对齐为每个有限索引 k 的前缀像输入域。packSteps 将分别给出的 Fin n 算子/矩阵数据配对，并证明两投影恢复原序列。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.Route"
        },
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.routeEquiv"
        },
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.routeWeight"
        },
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.AllPositive"
        },
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.HasZero"
        },
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.weight_zero_iff"
        },
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.weight_positive_iff"
        },
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.product_path_sum"
        },
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.one_step_paths"
        },
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.one_step_positive"
        }
      ],
      "representation": "正长度序列以 A::As 表示。Route I As.length 是所有中间索引的无约束笛卡尔积；routeEquiv 证明其与 Fin(n−1)→I 双射。起点 i、终点 j 为显式参数；权重递归乘上每条边。全正和含零分别逐边合取、析取。product_path_sum 证明对全部路径展开；n=1 的 Route I 0=Unit，只有一个空序列。",
      "dependencies": [
        "HC02-D03",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-D07",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.Channel"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.Row"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.Col"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.Diagonal"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.RowDecoupled"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.ColDecoupled"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.row_act"
        }
      ],
      "representation": "Channel=I×I；Row 固定输出 j，仅输入 i 可非零；Col 固定输入 i，仅输出 j 可非零；Diagonal 排除所有非对角项。RowDecoupled、ColDecoupled 都显式存在合法 Lip 证书及可能支撑位置。row_act 证明任意单行支撑的求和化简。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-D08",
      "status": "complete",
      "declarations": [
        {
          "file": "Scalar.lean",
          "name": "ChapterTwo.Scalars"
        },
        {
          "file": "Scalar.lean",
          "name": "ChapterTwo.scalarInf"
        }
      ],
      "representation": "Scalars 是只使用输入 i、输出 j 的所有 ENNReal 标量证书，scalarInf=sInf Scalars，空集下确界按 ENNReal 完备格取 ⊤。在原文 U⊆dom φ 上就是原定义；定义自然延伸到任意 U，不把它等同于矩阵条目。",
      "dependencies": []
    },
    {
      "id": "HC02-P01",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.singleton_lip"
        }
      ],
      "representation": "Subsingleton I 加显式 i 等价于 I={i}，将合法 Lip 求和化为唯一条目 L i i 的标量界。",
      "dependencies": [
        "HC02-D01"
      ]
    },
    {
      "id": "HC02-P02",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.global_restrict"
        }
      ],
      "representation": "对任意 U⊆dom φ，证明全域证书集合包含于受限证书集合。",
      "dependencies": [
        "HC02-D01",
        "HC02-P03"
      ]
    },
    {
      "id": "HC02-P03",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.lip_restrict"
        }
      ],
      "representation": "对 U⊆V，任意 V 上合法 Lip 证书仍在 U 上合法；V 的定义域条件来自该证书。",
      "dependencies": [
        "HC02-D01"
      ]
    },
    {
      "id": "HC02-P04",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.entryInf"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.entryInf_mono"
        }
      ],
      "representation": "entryInf 是受限合法矩阵集合在条目投影下的像集的 sInf；证明缩小 U 后此下确界不增，允许空证书族。",
      "dependencies": [
        "HC02-D01",
        "HC02-P03"
      ]
    },
    {
      "id": "HC02-P05",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.lip_comp"
        }
      ],
      "representation": "U 包含于 g∘f 的定义域，第二步域精确为 fU；两个局部证书导出 composeMat B A 的复合 Lip 界。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P06",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.colip_zero"
        }
      ],
      "representation": "更一般地对任意合法局部 CoLip 证书，输出零距且输入正距的点对迫使该通道系数为零；取 U=dom φ 得全域命题。",
      "dependencies": [
        "HC02-D02"
      ]
    },
    {
      "id": "HC02-P07",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.colip_comp"
        }
      ],
      "representation": "与 P05 同一实际像域；两个 CoLip 单步证书推出复合 CoLip 证书，初始域非空性由第一步证书保留。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P08",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.perturb_forward"
        }
      ],
      "representation": "从每分量的扩展伪度量对称性和三角不等式、逐点 δ 界，证明全部 x,y∈U 的正向像距界，误差写成 δj+δj。事实上不需要合法域假设，故特别覆盖原文公共定义域。",
      "dependencies": []
    },
    {
      "id": "HC02-P09",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.perturb_reverse"
        }
      ],
      "representation": "利用对称性交换两算子，并调用正向扰动定理，得反向像距界。",
      "dependencies": [
        "HC02-P08"
      ]
    },
    {
      "id": "HC02-P10",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.perturb_lip"
        }
      ],
      "representation": "在正向像距界中代入 φ1 的合法 Lip 矩阵上界；误差用 ENNReal 等式 2δ=δ+δ 表示。",
      "dependencies": [
        "HC02-D01",
        "HC02-P08"
      ]
    },
    {
      "id": "HC02-P11",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.perturb_colip"
        }
      ],
      "representation": "将 φ1 的 CoLip 求和下界与反向像距界传递连接，得到 φ2 输出距加 2δ 的上界。",
      "dependencies": [
        "HC02-D02",
        "HC02-P09"
      ]
    },
    {
      "id": "HC02-P12",
      "status": "complete",
      "declarations": [
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.chain_lip"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.chain_lip_stages"
        }
      ],
      "representation": "对任意列表长度归纳，以两步复合律证明所选矩阵有序乘积是完整复合的合法 Lip 证书；stages 版本接收每个原始单步在实际前缀像域上的假设。包含全部正长度及更强的零长度情形。",
      "dependencies": [
        "HC02-D01",
        "HC02-D03",
        "HC02-D04",
        "HC02-D05",
        "HC02-P05",
        "HC02-P14"
      ]
    },
    {
      "id": "HC02-P13",
      "status": "complete",
      "declarations": [
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.chain_colip"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.chain_colip_positive_length"
        },
        {
          "file": "Chains.lean",
          "name": "ChapterTwo.chain_colip_stages"
        }
      ],
      "representation": "同样归纳得到指定 CoLip 乘积。正长度版本由第一步合法性导出 U 非空，无额外非空假设；stages 版本直接接收逐步实际输入域上的 CoLip 数据。",
      "dependencies": [
        "HC02-D02",
        "HC02-D03",
        "HC02-D04",
        "HC02-D05",
        "HC02-P07",
        "HC02-P15"
      ]
    },
    {
      "id": "HC02-P14",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.identity_lip"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.act_unit"
        }
      ],
      "representation": "恒等算子在其定义域的任意子集上有单位 Lip 证书；act_unit 证明逐分量求和恒等式。因结论对空集也成立，原文非空 U 是特例。",
      "dependencies": [
        "HC02-D01",
        "HC02-D04"
      ]
    },
    {
      "id": "HC02-P15",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.identity_colip"
        }
      ],
      "representation": "对于非空 U⊆dom id，单位矩阵是合法 CoLip 证书。",
      "dependencies": [
        "HC02-D02",
        "HC02-D04",
        "HC02-P14"
      ]
    },
    {
      "id": "HC02-P16",
      "status": "complete",
      "declarations": [
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.product_zero_iff"
        },
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.one_step_paths"
        }
      ],
      "representation": "对任意非空系数列表证明乘积条目为零 iff 每个完整中间索引序列含零边，因此适用于所有所选合法 Lip 链证书；不需要额外正性或最优性。单步空路径边界独立列出。",
      "dependencies": [
        "HC02-D03",
        "HC02-D04",
        "HC02-D06"
      ]
    },
    {
      "id": "HC02-P17",
      "status": "complete",
      "declarations": [
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.product_positive_iff"
        },
        {
          "file": "Paths.lean",
          "name": "ChapterTwo.one_step_positive"
        }
      ],
      "representation": "对任意非空系数列表证明乘积条目正 iff 存在全边正的完整路径，因此适用于所有所选合法 CoLip 链证书；包括单步唯一空中间序列。",
      "dependencies": [
        "HC02-D03",
        "HC02-D04",
        "HC02-D06"
      ]
    },
    {
      "id": "HC02-P18",
      "status": "complete",
      "declarations": [
        {
          "file": "Scalar.lean",
          "name": "ChapterTwo.impossible_channel"
        }
      ],
      "representation": "给定 U 内输入零距而输出正距的点对，证明 Scalars=∅ 且 scalarInf=⊤；对 λ=⊤ 同样使用 λ·0=0。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P19",
      "status": "complete",
      "declarations": [
        {
          "file": "Scalar.lean",
          "name": "ChapterTwo.positive_finite_inf_attained"
        }
      ],
      "representation": "0<a<⊤ 时证明 a 属于整个标量可行集。输入距为 0、⊤、非零有限分别处理；有限非零分支使用 ENNReal 除法保序与 le_sInf，不把下确界可行性作为假设。",
      "dependencies": [
        "HC02-D08",
        "HC02-P24"
      ]
    },
    {
      "id": "HC02-P20",
      "status": "complete",
      "declarations": [
        {
          "file": "Scalar.lean",
          "name": "ChapterTwo.scalars_upward"
        }
      ],
      "representation": "任意可行 a 和 b≥a 都给出 b 可行，包含无限距离与无限系数。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P21",
      "status": "complete",
      "declarations": [
        {
          "file": "Scalar.lean",
          "name": "ChapterTwo.above_inf_feasible"
        }
      ],
      "representation": "证明更强结论：任意 a>scalarInf 都可行，不必预先限制下确界正或有限，且 a 可为 ⊤。证明使用 sInf_lt_iff 找到较小可行值再向上封闭。",
      "dependencies": [
        "HC02-D08",
        "HC02-P20"
      ]
    },
    {
      "id": "HC02-P22",
      "status": "complete",
      "declarations": [
        {
          "file": "Scalar.lean",
          "name": "ChapterTwo.zero_inf_positive"
        }
      ],
      "representation": "scalarInf=0 时每个正系数都可行，包含原文要求的每个有限正常数；不声称零可行。",
      "dependencies": [
        "HC02-D08",
        "HC02-P21"
      ]
    },
    {
      "id": "HC02-P23",
      "status": "complete",
      "declarations": [
        {
          "file": "Counterexample.lean",
          "name": "ChapterTwo.CounterX"
        },
        {
          "file": "Counterexample.lean",
          "name": "ChapterTwo.counterDist"
        },
        {
          "file": "Counterexample.lean",
          "name": "ChapterTwo.counterMetric"
        },
        {
          "file": "Counterexample.lean",
          "name": "ChapterTwo.counterOp"
        },
        {
          "file": "Counterexample.lean",
          "name": "ChapterTwo.counterDomain"
        },
        {
          "file": "Counterexample.lean",
          "name": "ChapterTwo.counterDomain_nonempty"
        },
        {
          "file": "Counterexample.lean",
          "name": "ChapterTwo.counterDomain_legal"
        },
        {
          "file": "Counterexample.lean",
          "name": "ChapterTwo.counter_positive_feasible"
        },
        {
          "file": "Counterexample.lean",
          "name": "ChapterTwo.counter_zero_infeasible"
        },
        {
          "file": "Counterexample.lean",
          "name": "ChapterTwo.counter_inf_zero"
        },
        {
          "file": "Counterexample.lean",
          "name": "ChapterTwo.zero_inf_not_attained_example"
        }
      ],
      "representation": "显式三点空间 Option Bool，吸收元 none；两普通点在输入 false 分量距离为 ⊤，输出 true 分量距离为 1，两分量都隔离吸收元。恒等算子，U 为两个普通点。完整证明全部扩展伪度量公理、合法域与非空性，并证明所有正系数可行、下确界为 0、系数 0 不可行。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P24",
      "status": "complete",
      "declarations": [
        {
          "file": "Scalar.lean",
          "name": "ChapterTwo.finite_inf_iff"
        }
      ],
      "representation": "完整等价 scalarInf<⊤ iff 存在全部点对合法的有限系数；直接由完备线性序的 sInf_lt_iff 证明，无下确界取到假设。",
      "dependencies": [
        "HC02-D08"
      ]
    },
    {
      "id": "HC02-P25",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.zero_term"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.delete_zero_term"
        }
      ],
      "representation": "条目为零时对任意距离向量该项为零，并证明总和等于删除该输入索引后的和，包含输入距 ⊤。",
      "dependencies": [
        "HC02-D03"
      ]
    },
    {
      "id": "HC02-P26",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.row_bound"
        }
      ],
      "representation": "合法 Lip 证书只要满足 Row A i j，就给出输出 j 相对任意唯一输入 i 的单项界，不要求 i=j。",
      "dependencies": [
        "HC02-D01",
        "HC02-D07"
      ]
    },
    {
      "id": "HC02-P27",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.col_contribution"
        }
      ],
      "representation": "Col A i j 保证每个 k≠j 的 A i k·v i=0，准确表达所选证书的贡献范围，而不是算子内在独立性。",
      "dependencies": [
        "HC02-D07",
        "HC02-P25"
      ]
    },
    {
      "id": "HC02-P28",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.diagonal_bound"
        }
      ],
      "representation": "Diagonal A 将每个输出行化为其对角输入项，从合法 Lip 证书得到所有分量的标量界。",
      "dependencies": [
        "HC02-D01",
        "HC02-D07",
        "HC02-P26"
      ]
    },
    {
      "id": "HC02-P29",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.two_sided"
        }
      ],
      "representation": "只对上界矩阵要求 Row A j j，下界矩阵无需稀疏性；从 CoLip 非负和抽取 B j j·dj，再与上界单行化简合并。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D07",
        "HC02-P26"
      ]
    },
    {
      "id": "HC02-P30",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.all_two_sided"
        },
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.finite_two_sided"
        }
      ],
      "representation": "对所有 j 的行条件给出所有分量双侧界；finite_two_sided 另外保留每个上下界对角系数 <⊤，得有限标量系数的双侧界，不误称距离本身有限。",
      "dependencies": [
        "HC02-D01",
        "HC02-D02",
        "HC02-D07",
        "HC02-P29"
      ]
    },
    {
      "id": "HC02-P31",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.positive_channel"
        }
      ],
      "representation": "任意通道 i→j 系数正和输入距正，利用 ENNReal 乘法正性与 CoLip 单项下界推出输出距正。",
      "dependencies": [
        "HC02-D02"
      ]
    },
    {
      "id": "HC02-P32",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "ChapterTwo.reflects_zero"
        }
      ],
      "representation": "全对角 CoLip 系数正时，输出的原前置模块 GaugeZeroRelated 蕴含输入的 GaugeZeroRelated；没有把族零距升级为点相等。",
      "dependencies": [
        "HC02-D02",
        "HC02-P31"
      ]
    }
  ]
}
```

**完成声明**：已完整完成并按冻结原文及 40 项清单对齐整章。未完成范围：无。未确认的数学证明或编译范围：无。所有新增目标源文件均在上文全文列出；前置模块保持冻结。
