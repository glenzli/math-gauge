# LCH02 完整形式化

入口为 `Main.lean`，导入全部三个目标模块；`Audit.lean` 是公理依赖核验入口。下列代码块给出全部新增源码和构建脚本。使用题目提供的 `lean-local`，运行 `sh build.sh`。

表示约定：矩阵 `M j i` 表示正文的输入 i 到输出 j；有限链内部从零编号，正文第 m+1 步对应 Lean 的 m。实际中间域定义为前缀复合的像，并证明其递推等式、非空性和定义域有效性。`Fin n` 版本不要求无限序列数据；辅助扩展的尾部不影响任何前缀。路径同时提供递归表示与通常的有限顶点序列表示。

本清单的证明只使用 ENNReal 的有限和、乘法和序结构，不需要伪度量公理。因此声明对任意分量函数 d 成立，取正文的有限非空扩展伪度量族即可直接特化。`DecidableEq I` 只是单位矩阵所需的判等数据，经典逻辑下对任意 I 可得；并无额外数学限制。Co-Lip 定义始终显式保留非空性。

验证：Lean 4.29.1，在提供的固定 mathlib 环境中编译全部模块并运行公理审计。所有新增声明的公理依赖均包含于 `propext`、`Classical.choice`、`Quot.sound`。

数学内容归属：Zhe Li（Glen Li / glenzli），ORCID https://orcid.org/0009-0006-6536-3453，《The Operator Evolution Theory》第一卷，第 2 章，https://glenzli.com/books/oet/ ，CC BY 4.0（https://creativecommons.org/licenses/by/4.0/）。题目来源版本 v1.0.0，DOI https://doi.org/10.5281/zenodo.21457931，源提交 539b40cec73184d98e06d54fbd10e4b4698bd6e7。下列为新写的 Lean 形式化，原有数学内容不是本回答独立发现；冻结前置模块保持不变，不重复交付。

```lean filename=Bounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic

/-
Source mathematics: Zhe Li (Glen Li / glenzli), The Operator Evolution Theory,
Volume I, Chapter 2, CC BY 4.0. This file is a new formalization.
-/
noncomputable section
namespace LCH02
open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators

variable {I X : Type} [Fintype I] {bot : X}

/-- Output index first, input index second: `M j i` is the entry i → j. -/
abbrev Mat (I : Type) := Matrix I I ENNReal

/-- Matrix action on a vector of component distances. -/
def act (M : Mat I) (v : I → ENNReal) (j : I) : ENNReal := ∑ i, M j i * v i

/-- The conventional product has the required order: B acts after A. -/
theorem matrix_mul_entry (B A : Mat I) (j i : I) :
    (B * A) j i = ∑ k, B j k * A k i := rfl

theorem act_mul (B A : Mat I) (v : I → ENNReal) (j : I) :
    act (B * A) v j = act B (fun k => act A v k) j := by
  simp only [act, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem act_mono (M : Mat I) {v w : I → ENNReal} (h : ∀ i, v i ≤ w i) (j : I) :
    act M v j ≤ act M w j :=
  Finset.sum_le_sum fun i _ => mul_le_mul_left' (h i) (M j i)

/-- Domain validity is included in restricted membership. Empty Lip domains are allowed. -/
def Lip (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (L : Mat I) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ act L (fun i => d i x y) j

def LipFamily (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {L | Lip d φ U L}

def GlobalLipFamily (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  LipFamily d φ (dom φ)

/-- Co-Lip membership includes the source's mandatory nonempty domain. -/
def CoLip (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (K : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    act K (fun i => d i x y) j ≤ d j (φ.func x) (φ.func y)

def CoLipFamily (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {K | CoLip d φ U K}

def GlobalCoLipFamily (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  CoLipFamily d φ (dom φ)

theorem lip_antitone (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U V : Set X} (hUV : U ⊆ V) : LipFamily d φ V ⊆ LipFamily d φ U := by
  intro L hL
  exact ⟨hUV.trans hL.1, fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

theorem global_lip_restrict (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U : Set X} (hU : U ⊆ dom φ) : GlobalLipFamily d φ ⊆ LipFamily d φ U :=
  lip_antitone d φ hU

theorem colip_antitone (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U V : Set X} (hU : U.Nonempty) (hUV : U ⊆ V) :
    CoLipFamily d φ V ⊆ CoLipFamily d φ U := by
  intro K hK
  exact ⟨hU, hUV.trans hK.2.1, fun x hx y hy j => hK.2.2 x (hUV hx) y (hUV hy) j⟩

theorem global_colip_restrict (d : I → X → X → ENNReal) (φ : Operator X bot)
    {U : Set X} (hne : U.Nonempty) (hU : U ⊆ dom φ) :
    GlobalCoLipFamily d φ ⊆ CoLipFamily d φ U := colip_antitone d φ hne hU

/-- For a singleton index type the entire global predicate is exactly the scalar bound. -/
theorem singleton_lip_iff [Unique I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (L : Mat I) (i : I) :
    L ∈ GlobalLipFamily d φ ↔ ∀ x ∈ dom φ, ∀ y ∈ dom φ,
      d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have hact : ∀ v : I → ENNReal, ∀ j, act L v j = L j i * v i := by
    intro v j
    simp [act, Finset.univ_unique, Unique.eq_default i]
  constructor
  · intro h x hx y hy
    simpa only [hact] using h.2 x hx y hy i
  · intro h
    refine ⟨Set.Subset.rfl, ?_⟩
    intro x hx y hy j
    have hj : j = i := Subsingleton.elim _ _
    simpa only [hj, hact] using h x hx y hy

/-- Domain facts forced by the absorption law, with the exact intermediate image. -/
theorem compose_domains (ψ φ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (ψ * φ)) : U ⊆ dom φ ∧ φ.func '' U ⊆ dom ψ := by
  constructor
  · intro x hx hbot
    have h := hU hx
    change ψ.func (φ.func x) ≠ bot at h
    rw [hbot, ψ.preserves_bot] at h
    exact h rfl
  · rintro y ⟨x, hx, rfl⟩
    exact hU hx

theorem lip_compose (d : I → X → X → ENNReal) (ψ φ : Operator X bot)
    {U : Set X} {A B : Mat I} (hU : U ⊆ dom (ψ * φ))
    (hA : Lip d φ U A) (hB : Lip d ψ (φ.func '' U) B) :
    Lip d (ψ * φ) U (B * A) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (ψ.func (φ.func x)) (ψ.func (φ.func y)) ≤ _
  calc
    _ ≤ act B (fun k => d k (φ.func x) (φ.func y)) j :=
      hB.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j
    _ ≤ act B (fun k => act A (fun i => d i x y) k) j :=
      act_mono B (hA.2 x hx y hy) j
    _ = act (B * A) (fun i => d i x y) j := (act_mul B A _ j).symm

theorem colip_compose (d : I → X → X → ENNReal) (ψ φ : Operator X bot)
    {U : Set X} {A B : Mat I} (hU : U ⊆ dom (ψ * φ))
    (hA : CoLip d φ U A) (hB : CoLip d ψ (φ.func '' U) B) :
    CoLip d (ψ * φ) U (B * A) := by
  refine ⟨hA.1, hU, ?_⟩
  intro x hx y hy j
  change _ ≤ d j (ψ.func (φ.func x)) (ψ.func (φ.func y))
  calc
    _ = act B (fun k => act A (fun i => d i x y) k) j := act_mul B A _ j
    _ ≤ act B (fun k => d k (φ.func x) (φ.func y)) j :=
      act_mono B (hA.2.2 x hx y hy) j
    _ ≤ _ := hB.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j

theorem colip_entry_zero (d : I → X → X → ENNReal) (φ : Operator X bot)
    {K : Mat I} (hK : K ∈ GlobalCoLipFamily d φ)
    {x y : X} (hx : x ∈ dom φ) (hy : y ∈ dom φ) {i j : I}
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K j i = 0 := by
  have hb := hK.2.2 x hx y hy j
  rw [hout] at hb
  have ht : K j i * d i x y ≤ 0 :=
    (Finset.single_le_sum (fun k _ => zero_le (K j k * d k x y)) (Finset.mem_univ i)).trans hb
  have hz : K j i * d i x y = 0 := le_antisymm ht (zero_le _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hin)

section Identity
variable [DecidableEq I]

theorem act_one (v : I → ENNReal) (j : I) : act (1 : Mat I) v j = v j := by
  simp [act, Matrix.one_apply]

theorem identity_lip (d : I → X → X → ENNReal) {U : Set X}
    (hU : U ⊆ dom (1 : Operator X bot)) : Lip d (1 : Operator X bot) U (1 : Mat I) := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simpa only [act_one] using (le_refl (d j x y))

theorem identity_colip (d : I → X → X → ENNReal) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom (1 : Operator X bot)) : CoLip d (1 : Operator X bot) U (1 : Mat I) := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  simpa only [act_one] using (le_refl (d j x y))
end Identity
end LCH02
```

```lean filename=Chains.lean
import Bounds

noncomputable section
namespace LCH02
open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators
variable {I X : Type} [Fintype I] [DecidableEq I] {bot : X}

/-- Chronological sequence, indexed from zero. The last step multiplies on the left. -/
def matrixProduct (M : ℕ → Mat I) : ℕ → Mat I
  | 0 => 1
  | n + 1 => M n * matrixProduct M n

/-- `composition φ n = φ(n-1) ∘ ... ∘ φ(0)`. -/
def composition (φ : ℕ → Operator X bot) : ℕ → Operator X bot
  | 0 => 1
  | n + 1 => φ n * composition φ n

/-- `imageDomain φ U m` is the actual input domain of step `m` (textual U_(m+1)). -/
def imageDomain (φ : ℕ → Operator X bot) (U : Set X) (m : ℕ) : Set X :=
  (composition φ m).func '' U

@[simp] theorem matrixProduct_zero (M : ℕ → Mat I) : matrixProduct M 0 = 1 := rfl
@[simp] theorem matrixProduct_succ (M : ℕ → Mat I) (n : ℕ) :
    matrixProduct M (n+1) = M n * matrixProduct M n := rfl
@[simp] theorem matrixProduct_one (M : ℕ → Mat I) : matrixProduct M 1 = M 0 := by
  simp [matrixProduct]
@[simp] theorem composition_zero (φ : ℕ → Operator X bot) : composition φ 0 = 1 := rfl
@[simp] theorem composition_succ (φ : ℕ → Operator X bot) (n : ℕ) :
    composition φ (n+1) = φ n * composition φ n := rfl
@[simp] theorem imageDomain_zero (φ : ℕ → Operator X bot) (U : Set X) :
    imageDomain φ U 0 = U := by
  change id '' U = U
  exact Set.image_id U

theorem imageDomain_succ (φ : ℕ → Operator X bot) (U : Set X) (n : ℕ) :
    imageDomain φ U (n+1) = (φ n).func '' imageDomain φ U n := by
  exact (Set.image_image (φ n).func (composition φ n).func U).symm

theorem imageDomain_nonempty (φ : ℕ → Operator X bot) {U : Set X}
    (hU : U.Nonempty) (m : ℕ) : (imageDomain φ U m).Nonempty :=
  hU.image _

/-- The domain of a full composition forces the validity of every earlier prefix. -/
theorem prefix_domain (φ : ℕ → Operator X bot) {U : Set X} {n : ℕ}
    (hU : U ⊆ dom (composition φ n)) {m : ℕ} (hm : m ≤ n) :
    U ⊆ dom (composition φ m) := by
  induction n with
  | zero => simpa only [Nat.eq_zero_of_le_zero hm] using hU
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hm with h | h
    · simpa only [h] using hU
    · exact ih (compose_domains (φ n) (composition φ n) hU).1 (Nat.le_of_lt_succ h)

/-- In particular the recursively generated actual input domain is valid for its step. -/
theorem step_domain (φ : ℕ → Operator X bot) {U : Set X} {n m : ℕ}
    (hU : U ⊆ dom (composition φ n)) (hm : m < n) :
    imageDomain φ U m ⊆ dom (φ m) :=
  (compose_domains (φ m) (composition φ m) (prefix_domain φ hU hm)).2

/-- All finite lengths, including zero; hypotheses are only the individual step inequalities. -/
theorem lip_chain (d : I → X → X → ENNReal) (φ : ℕ → Operator X bot)
    (M : ℕ → Mat I) (U : Set X) (n : ℕ)
    (hU : U ⊆ dom (composition φ n))
    (hsteps : ∀ m < n, Lip d (φ m) (imageDomain φ U m) (M m)) :
    Lip d (composition φ n) U (matrixProduct M n) := by
  induction n with
  | zero => exact identity_lip d hU
  | succ n ih =>
    apply lip_compose d (φ n) (composition φ n) hU
    · apply ih (compose_domains (φ n) (composition φ n) hU).1
      intro m hm
      exact hsteps m (Nat.lt.step hm)
    · exact hsteps n (Nat.lt_succ_self n)

/-- The nonempty-domain variant includes the zero-step case. -/
theorem colip_chain (d : I → X → X → ENNReal) (φ : ℕ → Operator X bot)
    (M : ℕ → Mat I) (U : Set X) (n : ℕ) (hne : U.Nonempty)
    (hU : U ⊆ dom (composition φ n))
    (hsteps : ∀ m < n, CoLip d (φ m) (imageDomain φ U m) (M m)) :
    CoLip d (composition φ n) U (matrixProduct M n) := by
  induction n with
  | zero => exact identity_colip d hne hU
  | succ n ih =>
    apply colip_compose d (φ n) (composition φ n) hU
    · apply ih (compose_domains (φ n) (composition φ n) hU).1
      intro m hm
      exact hsteps m (Nat.lt.step hm)
    · exact hsteps n (Nat.lt_succ_self n)

/-- For positive length the first step certificate already supplies nonemptiness. -/
theorem colip_chain_positive (d : I → X → X → ENNReal) (φ : ℕ → Operator X bot)
    (M : ℕ → Mat I) (U : Set X) (n : ℕ) (hn : 0 < n)
    (hU : U ⊆ dom (composition φ n))
    (hsteps : ∀ m < n, CoLip d (φ m) (imageDomain φ U m) (M m)) :
    CoLip d (composition φ n) U (matrixProduct M n) := by
  apply colip_chain d φ M U n _ hU hsteps
  simpa only [imageDomain_zero] using (hsteps 0 hn).1

/-- No assumption or value beyond the finite prefix affects the composite. -/
theorem composition_prefix_congr (φ ψ : ℕ → Operator X bot) (n : ℕ)
    (h : ∀ m < n, φ m = ψ m) : composition φ n = composition ψ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [composition_succ, h n (Nat.lt_succ_self n),
      ih (fun m hm => h m (Nat.lt.step hm))]

theorem matrixProduct_prefix_congr (M N : ℕ → Mat I) (n : ℕ)
    (h : ∀ m < n, M m = N m) : matrixProduct M n = matrixProduct N n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [matrixProduct_succ, h n (Nat.lt_succ_self n),
      ih (fun m hm => h m (Nat.lt.step hm))]

/-- Any finite family extends to the indexing convention used here, without extra hypotheses. -/
def extendFinite {α : Type} (fallback : α) {n : ℕ} (f : Fin n → α) (m : ℕ) : α :=
  if h : m < n then f ⟨m, h⟩ else fallback

theorem extendFinite_at {α : Type} (fallback : α) {n : ℕ} (f : Fin n → α) (m : Fin n) :
    extendFinite fallback f m = f m := by simp [extendFinite, m.isLt]

/-- A fully finite-input formulation of the Lip theorem. -/
theorem finite_lip_chain (d : I → X → X → ENNReal) {n : ℕ}
    (φ : Fin n → Operator X bot) (M : Fin n → Mat I) (U : Set X)
    (hU : U ⊆ dom (composition (extendFinite 1 φ) n))
    (hsteps : ∀ m : Fin n,
      Lip d (φ m) (imageDomain (extendFinite 1 φ) U m) (M m)) :
    Lip d (composition (extendFinite 1 φ) n) U
      (matrixProduct (extendFinite 1 M) n) := by
  apply lip_chain d _ _ U n hU
  intro m hm
  simpa only [extendFinite, dif_pos hm] using hsteps ⟨m, hm⟩

theorem finite_colip_chain (d : I → X → X → ENNReal) {n : ℕ} (hn : 0 < n)
    (φ : Fin n → Operator X bot) (M : Fin n → Mat I) (U : Set X)
    (hU : U ⊆ dom (composition (extendFinite 1 φ) n))
    (hsteps : ∀ m : Fin n,
      CoLip d (φ m) (imageDomain (extendFinite 1 φ) U m) (M m)) :
    CoLip d (composition (extendFinite 1 φ) n) U
      (matrixProduct (extendFinite 1 M) n) := by
  apply colip_chain_positive d _ _ U n hn hU
  intro m hm
  simpa only [extendFinite, dif_pos hm] using hsteps ⟨m, hm⟩
end LCH02
```

```lean filename=Paths.lean
import Chains

noncomputable section
namespace LCH02
open scoped BigOperators
variable {I : Type} [Fintype I] [DecidableEq I]

/-- A finite path with fixed endpoints, built by appending one edge.
A length-zero path is endpoint equality. A length-(n+1) path chooses the
penultimate index k freely and a length-n path from i to k. Thus, for positive
length, these are precisely all choices of the n-1 intermediate indices. -/
def IndexPath (I : Type) : ℕ → I → I → Type
  | 0, i, j => PLift (i = j)
  | n+1, i, _ => Σ k : I, IndexPath I n i k

/-- Every step along this particular path has strictly positive entry. -/
def AllPositive (M : ℕ → Mat I) : {n : ℕ} → {i j : I} → IndexPath I n i j → Prop
  | 0, _, _, _ => True
  | n+1, _, j, p => AllPositive M p.2 ∧ 0 < M n j p.1

/-- At least one of this path's step entries is zero. -/
def HasZero (M : ℕ → Mat I) : {n : ℕ} → {i j : I} → IndexPath I n i j → Prop
  | 0, _, _, _ => False
  | n+1, _, j, p => HasZero M p.2 ∨ M n j p.1 = 0

/-- The concrete sequence of step coefficients has length exactly n. -/
def edgeEntry (M : ℕ → Mat I) : {n : ℕ} → {i j : I} → IndexPath I n i j → Fin n → ENNReal
  | 0, _, _, _ => Fin.elim0
  | n+1, _, j, p => Fin.lastCases (M n j p.1) (edgeEntry M p.2)

theorem allPositive_iff_edges (M : ℕ → Mat I) {n : ℕ} {i j : I}
    (p : IndexPath I n i j) : AllPositive M p ↔ ∀ m, 0 < edgeEntry M p m := by
  induction n generalizing j with
  | zero => simp [AllPositive, edgeEntry]
  | succ n ih =>
    change (AllPositive M p.2 ∧ 0 < M n j p.1) ↔ _
    rw [ih]
    constructor
    · rintro ⟨h, hl⟩ m
      refine Fin.lastCases ?_ (fun k => ?_) m
      · simpa only [edgeEntry, Fin.lastCases_last] using hl
      · simpa only [edgeEntry, Fin.lastCases_castSucc] using h k
    · intro h
      exact ⟨fun k => by simpa only [edgeEntry, Fin.lastCases_castSucc] using h k.castSucc,
        by simpa only [edgeEntry, Fin.lastCases_last] using h (Fin.last n)⟩

theorem hasZero_iff_edges (M : ℕ → Mat I) {n : ℕ} {i j : I}
    (p : IndexPath I n i j) : HasZero M p ↔ ∃ m, edgeEntry M p m = 0 := by
  induction n generalizing j with
  | zero => simp [HasZero, edgeEntry]
  | succ n ih =>
    change (HasZero M p.2 ∨ M n j p.1 = 0) ↔ _
    rw [ih]
    constructor
    · rintro (⟨k, hk⟩ | hl)
      · exact ⟨k.castSucc, by simpa only [edgeEntry, Fin.lastCases_castSucc] using hk⟩
      · exact ⟨Fin.last n, by simpa only [edgeEntry, Fin.lastCases_last] using hl⟩
    · rintro ⟨m, hm⟩
      revert hm
      refine Fin.lastCases ?_ (fun k => ?_) m
      · intro h
        exact Or.inr (by simpa only [edgeEntry, Fin.lastCases_last] using h)
      · intro h
        exact Or.inl ⟨k, by simpa only [edgeEntry, Fin.lastCases_castSucc] using h⟩

theorem hasZero_iff_not_allPositive (M : ℕ → Mat I) {n : ℕ} {i j : I}
    (p : IndexPath I n i j) : HasZero M p ↔ ¬ AllPositive M p := by
  rw [hasZero_iff_edges, allPositive_iff_edges]
  simp only [not_forall, not_lt, nonpos_iff_eq_zero]

/-- Positive product entries are exactly those admitting an all-positive path.
The theorem also handles length zero, where the matrix is the identity. -/
theorem product_pos_iff (M : ℕ → Mat I) (n : ℕ) (i j : I) :
    0 < matrixProduct M n j i ↔ ∃ p : IndexPath I n i j, AllPositive M p := by
  induction n generalizing j with
  | zero =>
    by_cases h : i = j
    · subst j
      simp [matrixProduct, Matrix.one_apply, IndexPath, AllPositive]
    · simp [matrixProduct, Matrix.one_apply, IndexPath, AllPositive, h, Ne.symm h]
  | succ n ih =>
    simp only [matrixProduct_succ, Matrix.mul_apply, Finset.sum_pos_iff,
      Finset.mem_univ, true_and, ENNReal.mul_pos_iff, ih]
    constructor
    · rintro ⟨k, hk, p, hp⟩
      exact ⟨⟨k, p⟩, hp, hk⟩
    · rintro ⟨⟨k, p⟩, hp, hk⟩
      exact ⟨k, hk, p, hp⟩

/-- A product entry is zero iff every path has a zero step factor. -/
theorem product_zero_iff (M : ℕ → Mat I) (n : ℕ) (i j : I) :
    matrixProduct M n j i = 0 ↔ ∀ p : IndexPath I n i j, HasZero M p := by
  constructor
  · intro hz p
    apply (hasZero_iff_not_allPositive M p).2
    intro hp
    have h := (product_pos_iff M n i j).2 ⟨p, hp⟩
    simp only [hz, lt_self_iff_false] at h
  · intro h
    by_contra hn
    have hp : 0 < matrixProduct M n j i := pos_iff_ne_zero.mpr hn
    obtain ⟨p, hpos⟩ := (product_pos_iff M n i j).1 hp
    exact (hasZero_iff_not_allPositive M p).1 (h p) hpos

/-- Explicit one-step specialization: the intermediate sequence is empty. -/
theorem one_step_positive (M : ℕ → Mat I) (i j : I) :
    (∃ p : IndexPath I 1 i j, AllPositive M p) ↔ 0 < M 0 j i := by
  rw [← product_pos_iff, matrixProduct_one]

theorem one_step_zero (M : ℕ → Mat I) (i j : I) :
    (∀ p : IndexPath I 1 i j, HasZero M p) ↔ M 0 j i = 0 := by
  rw [← product_zero_iff, matrixProduct_one]

/-- Formulation with a genuinely finite matrix family. -/
theorem finite_product_pos_iff {n : ℕ} (M : Fin n → Mat I) (i j : I) :
    0 < matrixProduct (extendFinite 1 M) n j i ↔
      ∃ p : IndexPath I n i j, AllPositive (extendFinite 1 M) p :=
  product_pos_iff _ _ _ _

theorem finite_product_zero_iff {n : ℕ} (M : Fin n → Mat I) (i j : I) :
    matrixProduct (extendFinite 1 M) n j i = 0 ↔
      ∀ p : IndexPath I n i j, HasZero (extendFinite 1 M) p :=
  product_zero_iff _ _ _ _
end LCH02

namespace LCH02
variable {I : Type}

/-- The vertices underlying the recursive path, with both endpoints included. -/
def pathVertex : {n : ℕ} → {i j : I} → IndexPath I n i j → Fin (n+1) → I
  | 0, i, _, _, _ => i
  | n+1, _, j, p, t => Fin.lastCases j (pathVertex p.2) t

@[simp] theorem pathVertex_first {n : ℕ} {i j : I} (p : IndexPath I n i j) :
    pathVertex p 0 = i := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    change pathVertex p (0 : Fin (n+1)).castSucc = i
    simpa only [pathVertex, Fin.lastCases_castSucc] using ih p.2

@[simp] theorem pathVertex_last {n : ℕ} {i j : I} (p : IndexPath I n i j) :
    pathVertex p (Fin.last n) = j := by
  cases n with
  | zero => exact p.down
  | succ n => exact Fin.lastCases_last

/-- Conversely every vertex sequence gives a path, with no restriction on intermediate indices. -/
def pathFromVertices : (n : ℕ) → (v : Fin (n+1) → I) →
    IndexPath I n (v 0) (v (Fin.last n))
  | 0, _ => ⟨rfl⟩
  | n+1, v => ⟨v (Fin.last n).castSucc, pathFromVertices n (fun t => v t.castSucc)⟩

@[simp] theorem pathFromVertices_vertex (n : ℕ) (v : Fin (n+1) → I)
    (t : Fin (n+1)) : pathVertex (pathFromVertices n v) t = v t := by
  induction n with
  | zero => have ht : t = 0 := Fin.ext (by omega); subst t; rfl
  | succ n ih =>
    refine Fin.lastCases ?_ (fun k => ?_) t
    · exact pathVertex_last _
    · simpa only [pathFromVertices, pathVertex, Fin.lastCases_castSucc] using
        ih (fun t => v t.castSucc) k

/-- Edge m goes from vertex m to vertex m+1 in precisely matrix M(m). -/
theorem edgeEntry_vertices [Fintype I] [DecidableEq I] (M : ℕ → Mat I)
    {n : ℕ} {i j : I} (p : IndexPath I n i j) (m : Fin n) :
    edgeEntry M p m = M m (pathVertex p m.succ) (pathVertex p m.castSucc) := by
  induction n generalizing j with
  | zero => exact Fin.elim0 m
  | succ n ih =>
    refine Fin.lastCases ?_ (fun k => ?_) m
    · simp only [edgeEntry, Fin.lastCases_last]
      change M n j p.1 = M n (pathVertex p (Fin.last (n+1)))
        (pathVertex p (Fin.last n).castSucc)
      simp only [pathVertex_last, pathVertex, Fin.lastCases_castSucc, Fin.lastCases_last, pathVertex_last]
    · simpa only [edgeEntry, Fin.lastCases_castSucc, Fin.succ_castSucc, Fin.val_castSucc,
        pathVertex, Fin.lastCases_castSucc] using ih p.2 k

/-- The recursive positive predicate is exactly the ordinary quantification over all layers. -/
theorem allPositive_iff_vertices [Fintype I] [DecidableEq I] (M : ℕ → Mat I)
    {n : ℕ} {i j : I} (p : IndexPath I n i j) :
    AllPositive M p ↔ ∀ m : Fin n,
      0 < M m (pathVertex p m.succ) (pathVertex p m.castSucc) := by
  simp only [allPositive_iff_edges, edgeEntry_vertices]

theorem hasZero_iff_vertices [Fintype I] [DecidableEq I] (M : ℕ → Mat I)
    {n : ℕ} {i j : I} (p : IndexPath I n i j) :
    HasZero M p ↔ ∃ m : Fin n,
      M m (pathVertex p m.succ) (pathVertex p m.castSucc) = 0 := by
  simp only [hasZero_iff_edges, edgeEntry_vertices]
end LCH02

namespace LCH02
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Usual vertex-sequence statement, including fixed endpoints and all n edge conditions. -/
theorem product_pos_vertices_iff (M : ℕ → Mat I) (n : ℕ) (i j : I) :
    0 < matrixProduct M n j i ↔
      ∃ v : Fin (n+1) → I, v 0 = i ∧ v (Fin.last n) = j ∧
        ∀ m : Fin n, 0 < M m (v m.succ) (v m.castSucc) := by
  rw [product_pos_iff]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨pathVertex p, pathVertex_first p, pathVertex_last p,
      (allPositive_iff_vertices M p).1 hp⟩
  · rintro ⟨v, hi, hj, h⟩
    subst i
    subst j
    refine ⟨pathFromVertices n v, (allPositive_iff_vertices M _).2 ?_⟩
    simpa only [pathFromVertices_vertex] using h

/-- Usual zero criterion: each fixed-endpoint vertex sequence has a zero edge. -/
theorem product_zero_vertices_iff (M : ℕ → Mat I) (n : ℕ) (i j : I) :
    matrixProduct M n j i = 0 ↔
      ∀ v : Fin (n+1) → I, v 0 = i → v (Fin.last n) = j →
        ∃ m : Fin n, M m (v m.succ) (v m.castSucc) = 0 := by
  rw [product_zero_iff]
  constructor
  · intro h v hi hj
    subst i
    subst j
    have hz := (hasZero_iff_vertices M _).1 (h (pathFromVertices n v))
    simpa only [pathFromVertices_vertex] using hz
  · intro h p
    apply (hasZero_iff_vertices M p).2
    exact h (pathVertex p) (pathVertex_first p) (pathVertex_last p)
end LCH02

namespace LCH02
variable {I : Type} [Fintype I] [DecidableEq I]

theorem finite_product_pos_vertices_iff {n : ℕ} (M : Fin n → Mat I) (i j : I) :
    0 < matrixProduct (extendFinite 1 M) n j i ↔
      ∃ v : Fin (n+1) → I, v 0 = i ∧ v (Fin.last n) = j ∧
        ∀ m : Fin n, 0 < M m (v m.succ) (v m.castSucc) := by
  simpa only [extendFinite_at] using product_pos_vertices_iff (extendFinite 1 M) n i j

theorem finite_product_zero_vertices_iff {n : ℕ} (M : Fin n → Mat I) (i j : I) :
    matrixProduct (extendFinite 1 M) n j i = 0 ↔
      ∀ v : Fin (n+1) → I, v 0 = i → v (Fin.last n) = j →
        ∃ m : Fin n, M m (v m.succ) (v m.castSucc) = 0 := by
  simpa only [extendFinite_at] using product_zero_vertices_iff (extendFinite 1 M) n i j
end LCH02
```

```lean filename=Main.lean
import Bounds
import Chains
import Paths

/-!
LCH02 entrypoint. All twenty obligations are implemented in the three imported
modules. Frozen foundations are imported unchanged through Bounds.

Mathematical source: Zhe Li (Glen Li / glenzli), ORCID
https://orcid.org/0009-0006-6536-3453, The Operator Evolution Theory,
Volume I, Chapter 2, https://glenzli.com/books/oet/, CC BY 4.0.
These Lean proofs and representation choices are newly generated formalizations,
not claims of original authorship of the source mathematics.
-/
```

```lean filename=Audit.lean
import Main

-- Kernel dependency audit for every new declaration.
#print axioms LCH02.Mat
#print axioms LCH02.act
#print axioms LCH02.matrix_mul_entry
#print axioms LCH02.act_mul
#print axioms LCH02.act_mono
#print axioms LCH02.Lip
#print axioms LCH02.LipFamily
#print axioms LCH02.GlobalLipFamily
#print axioms LCH02.CoLip
#print axioms LCH02.CoLipFamily
#print axioms LCH02.GlobalCoLipFamily
#print axioms LCH02.lip_antitone
#print axioms LCH02.global_lip_restrict
#print axioms LCH02.colip_antitone
#print axioms LCH02.global_colip_restrict
#print axioms LCH02.singleton_lip_iff
#print axioms LCH02.compose_domains
#print axioms LCH02.lip_compose
#print axioms LCH02.colip_compose
#print axioms LCH02.colip_entry_zero
#print axioms LCH02.act_one
#print axioms LCH02.identity_lip
#print axioms LCH02.identity_colip
#print axioms LCH02.matrixProduct
#print axioms LCH02.composition
#print axioms LCH02.imageDomain
#print axioms LCH02.matrixProduct_zero
#print axioms LCH02.matrixProduct_succ
#print axioms LCH02.matrixProduct_one
#print axioms LCH02.composition_zero
#print axioms LCH02.composition_succ
#print axioms LCH02.imageDomain_zero
#print axioms LCH02.imageDomain_succ
#print axioms LCH02.imageDomain_nonempty
#print axioms LCH02.prefix_domain
#print axioms LCH02.step_domain
#print axioms LCH02.lip_chain
#print axioms LCH02.colip_chain
#print axioms LCH02.colip_chain_positive
#print axioms LCH02.composition_prefix_congr
#print axioms LCH02.matrixProduct_prefix_congr
#print axioms LCH02.extendFinite
#print axioms LCH02.extendFinite_at
#print axioms LCH02.finite_lip_chain
#print axioms LCH02.finite_colip_chain
#print axioms LCH02.IndexPath
#print axioms LCH02.AllPositive
#print axioms LCH02.HasZero
#print axioms LCH02.edgeEntry
#print axioms LCH02.allPositive_iff_edges
#print axioms LCH02.hasZero_iff_edges
#print axioms LCH02.hasZero_iff_not_allPositive
#print axioms LCH02.product_pos_iff
#print axioms LCH02.product_zero_iff
#print axioms LCH02.one_step_positive
#print axioms LCH02.one_step_zero
#print axioms LCH02.finite_product_pos_iff
#print axioms LCH02.finite_product_zero_iff
#print axioms LCH02.pathVertex
#print axioms LCH02.pathVertex_first
#print axioms LCH02.pathVertex_last
#print axioms LCH02.pathFromVertices
#print axioms LCH02.pathFromVertices_vertex
#print axioms LCH02.edgeEntry_vertices
#print axioms LCH02.allPositive_iff_vertices
#print axioms LCH02.hasZero_iff_vertices
#print axioms LCH02.product_pos_vertices_iff
#print axioms LCH02.product_zero_vertices_iff
#print axioms LCH02.finite_product_pos_vertices_iff
#print axioms LCH02.finite_product_zero_vertices_iff
```

```sh filename=build.sh
#!/bin/sh
set -eu
# Use the supplied pinned Lean 4.29.1 / mathlib environment.
./lean-local -o formal_oet/vol_01/ch_01_foundations/gauge_space.olean formal_oet/vol_01/ch_01_foundations/gauge_space.lean
./lean-local -o formal_oet/vol_01/ch_01_foundations/operator_space.olean formal_oet/vol_01/ch_01_foundations/operator_space.lean
./lean-local -o Bounds.olean Bounds.lean
./lean-local -o Chains.olean Chains.lean
./lean-local -o Paths.olean Paths.lean
./lean-local -o Main.olean Main.lean
./lean-local Audit.lean
```

```json filename=alignment.json
{
  "case_id": "LCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "CH02-D01",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.Lip"
        },
        {
          "file": "Bounds.lean",
          "name": "LCH02.LipFamily"
        },
        {
          "file": "Bounds.lean",
          "name": "LCH02.GlobalLipFamily"
        }
      ],
      "representation": {
        "objects": "Lip d φ U L 与受限 Lip 合法性对应；LipFamily 是全部合法矩阵的集合，GlobalLipFamily 在 dom φ 上取该集合。",
        "parameters": "沿用冻结的 Operator X bot 和 dom；d : I → X → X → ENNReal，I 有限；L j i 表示输入 i 到输出 j。",
        "quantifiers": "U ⊆ dom φ，且对所有 x,y ∈ U 和所有 j 成立；允许 U 为空。",
        "conclusion": "d j (φ x) (φ y) ≤ ∑ i, L j i * d i x y。全域情形取 U=dom φ。"
      },
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.CoLip"
        },
        {
          "file": "Bounds.lean",
          "name": "LCH02.CoLipFamily"
        },
        {
          "file": "Bounds.lean",
          "name": "LCH02.GlobalCoLipFamily"
        }
      ],
      "representation": {
        "objects": "CoLip 为受限 co-Lip 合法性，另两定义为受限及全域证书族。",
        "parameters": "同一 Operator、dom 和 ENNReal 矩阵表示。",
        "quantifiers": "显式包含 U.Nonempty 和 U ⊆ dom φ；所有 x,y ∈ U、所有输出 j。",
        "conclusion": "∑ i, K j i * d i x y ≤ d j (φ x) (φ y)，不指定极值矩阵。"
      },
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.Mat"
        },
        {
          "file": "Bounds.lean",
          "name": "LCH02.act"
        },
        {
          "file": "Bounds.lean",
          "name": "LCH02.matrix_mul_entry"
        },
        {
          "file": "Bounds.lean",
          "name": "LCH02.act_mul"
        }
      ],
      "representation": {
        "objects": "Mat I = Matrix I I ENNReal；先输出行 j，后输入列 i。act 为分量距离向量上的矩阵作用。",
        "parameters": "标准 mathlib Matrix 乘法；ENNReal 使用 0*∞=∞*0=0 的约定。",
        "quantifiers": "任意有限 I、矩阵 A B、输入 i 和输出 j。",
        "conclusion": "(B*A) j i = ∑ k, B j k * A k i；act_mul 验证对应的嵌套有限求和恒等式。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "Chains.lean",
          "name": "LCH02.matrixProduct"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.matrixProduct_zero"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.matrixProduct_succ"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.matrixProduct_one"
        }
      ],
      "representation": {
        "objects": "单位矩阵使用标准 (1 : Mat I)；matrixProduct 为按时间顺序的有限复合乘积。",
        "parameters": "M m 对应正文第 m+1 个矩阵。DecidableEq I 仅用于单位矩阵，经典逻辑可提供。",
        "quantifiers": "任意 n≥0；matrixProduct_prefix_congr 保证只依赖前 n 项。",
        "conclusion": "空乘积为 1，递推式为 P(n+1)=M(n)*P(n)，一项乘积为 M(0)。"
      },
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "Chains.lean",
          "name": "LCH02.composition"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.imageDomain"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.imageDomain_zero"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.imageDomain_succ"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.imageDomain_nonempty"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.prefix_domain"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.step_domain"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.composition_prefix_congr"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.extendFinite"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.extendFinite_at"
        }
      ],
      "representation": {
        "objects": "composition φ n 是 φ(n-1)∘…∘φ(0)，imageDomain φ U m 是其 m 步前缀的实际像。",
        "parameters": "φ(m) 对应正文 φ_(m+1)，imageDomain … m 对应 U_(m+1)，初始集合 U 对应 U_1。",
        "quantifiers": "U ⊆ dom(composition φ n) 时，对每个 m<n 推出实际输入域包含在 dom(φ m) 中。",
        "conclusion": "零步像为 U，下一步像精确等于 φ(m) 对当前域的像；非空性被像保留。Fin n 序列可通过 extendFinite 无额外假设地扩展，前缀不依赖扩展尾部。"
      },
      "dependencies": []
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "Paths.lean",
          "name": "LCH02.IndexPath"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.AllPositive"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.HasZero"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.edgeEntry"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.pathVertex"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.pathFromVertices"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.pathFromVertices_vertex"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.allPositive_iff_vertices"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.hasZero_iff_vertices"
        }
      ],
      "representation": {
        "objects": "IndexPath I n i j 是固定起终点、逐次追加边的长度 n 路径；AllPositive 和 HasZero 是逐边条件。",
        "parameters": "正文 k_0=i、k_n=j 对应 pathVertex p 0=i、pathVertex p (Fin.last n)=j；第 m+1 层使用 M m。",
        "quantifiers": "所有中间指标任意；pathFromVertices 接受任意 Fin(n+1) 顶点序列，且还原所有顶点，故不限制路径。",
        "conclusion": "全正等价于每个 m:Fin n 的 M m (v(m+1)) (v m)>0；含零等价于存在这样的 m 条目等于零。"
      },
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.singleton_lip_iff"
        }
      ],
      "representation": {
        "objects": "一元素指标集用 Unique I 表示，并显式指定其唯一元素 i。",
        "parameters": "任意 d、φ、L；Unique I 与非空且基数为 1 的集合等价。",
        "quantifiers": "所有 x,y ∈ dom φ。",
        "conclusion": "全域 Lip 合法性当且仅当单个标量不等式 d_i(φx,φy)≤L_ii d_i(x,y)。"
      },
      "dependencies": [
        "CH02-D01"
      ]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.lip_antitone"
        }
      ],
      "representation": {
        "objects": "证书族的集合包含关系直接用 Set.Subset 表示。",
        "parameters": "任意固定 d、φ、U、V，U⊆V；V 的定义域有效性由证书成员性携带。",
        "quantifiers": "对每一个 V 上合法的 L。",
        "conclusion": "同一 L 在 U 上合法，包括空 U。"
      },
      "dependencies": [
        "CH02-D01"
      ]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.compose_domains"
        },
        {
          "file": "Bounds.lean",
          "name": "LCH02.lip_compose"
        }
      ],
      "representation": {
        "objects": "ψ*φ 为先 φ 后 ψ，精确中间集合为 φ.func '' U。",
        "parameters": "U⊆dom(ψ*φ)，A 在 U 上是 φ 的证书，B 在 φ(U) 上是 ψ 的证书。",
        "quantifiers": "任意两个算子、矩阵和集合，对所有起始点对与输出分量。",
        "conclusion": "B*A 是 ψ*φ 在 U 上的 Lip 证书；compose_domains 同时推出两步所需的定义域包含。"
      },
      "dependencies": [
        "CH02-D01",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.colip_antitone"
        }
      ],
      "representation": {
        "objects": "含非空条件的 co-Lip 证书族反单调。",
        "parameters": "U.Nonempty、U⊆V，V 的定义域有效性由证书成员性携带。",
        "quantifiers": "每个 V 上合法的 K。",
        "conclusion": "K 在 U 上仍合法，保留 U 非空。"
      },
      "dependencies": [
        "CH02-D02"
      ]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.colip_entry_zero"
        }
      ],
      "representation": {
        "objects": "全域 co-Lip 矩阵的单个条目 K j i。",
        "parameters": "K 为全域证书，x,y∈dom φ，d_j(φx,φy)=0，0<d_i(x,y)。",
        "quantifiers": "任意这样的 K、点对和输入输出指标。",
        "conclusion": "K j i=0；证明使用单项不超过有限非负和及 ENNReal 的无零因子性质。"
      },
      "dependencies": [
        "CH02-D02"
      ]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.compose_domains"
        },
        {
          "file": "Bounds.lean",
          "name": "LCH02.colip_compose"
        }
      ],
      "representation": {
        "objects": "ψ*φ 与精确中间像 φ.func '' U，乘积顺序 B*A。",
        "parameters": "U⊆dom(ψ*φ)，A、B 分别为 U 与 φ(U) 上的 co-Lip 证书。",
        "quantifiers": "任意两个算子与证书，对所有起始点对和输出分量。",
        "conclusion": "B*A 是全复合在 U 上的 co-Lip 证书；非空性从第一步证书明确保留。"
      },
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.act_one"
        },
        {
          "file": "Bounds.lean",
          "name": "LCH02.identity_lip"
        }
      ],
      "representation": {
        "objects": "冻结算子幺半群的 1 是恒等算子，矩阵幺半群的 1 是单位矩阵。",
        "parameters": "U⊆dom(1 : Operator X bot)。",
        "quantifiers": "任意这样的 U；事实上不要求 U 非空，所以包含正文非空情形。",
        "conclusion": "单位矩阵为恒等算子的受限 Lip 证书。"
      },
      "dependencies": [
        "CH02-D01",
        "CH02-D04"
      ]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.act_one"
        },
        {
          "file": "Bounds.lean",
          "name": "LCH02.identity_colip"
        }
      ],
      "representation": {
        "objects": "同一个单位矩阵用于恒等算子的 co-Lip 下界。",
        "parameters": "U.Nonempty 且 U⊆dom(1 : Operator X bot)。",
        "quantifiers": "任意非空有效域 U 及其所有点对。",
        "conclusion": "单位矩阵为受限 co-Lip 证书，结合 P11 得到交集结论。"
      },
      "dependencies": [
        "CH02-D02",
        "CH02-D04"
      ]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {
          "file": "Paths.lean",
          "name": "LCH02.product_pos_iff"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.product_pos_vertices_iff"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.finite_product_pos_vertices_iff"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.one_step_positive"
        }
      ],
      "representation": {
        "objects": "最终有限族版本使用 M:Fin n→Mat I 和 v:Fin(n+1)→I，端点以等式指定。",
        "parameters": "M m 对应正文 M^(m+1)，矩阵条目顺序为输出行、输入列。",
        "quantifiers": "任意 n，故特别适用于所有 n≥1；存在顶点序列，且每个 m:Fin n 的边严格为正。",
        "conclusion": "乘积条目>0 当且仅当存在全正路径；one_step_positive 验证 n=1 的退化情况。"
      },
      "dependencies": [
        "CH02-D03",
        "CH02-D04",
        "CH02-D06"
      ]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.global_lip_restrict"
        }
      ],
      "representation": {
        "objects": "GlobalLipFamily 到 LipFamily 的包含。",
        "parameters": "U⊆dom φ。",
        "quantifiers": "任意全域合法的 Lip 矩阵。",
        "conclusion": "同一矩阵在 U 上合法。"
      },
      "dependencies": [
        "CH02-D01",
        "CH02-P02"
      ]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {
          "file": "Bounds.lean",
          "name": "LCH02.global_colip_restrict"
        }
      ],
      "representation": {
        "objects": "GlobalCoLipFamily 到 CoLipFamily 的包含。",
        "parameters": "U.Nonempty 且 U⊆dom φ。",
        "quantifiers": "任意全域合法的 co-Lip 矩阵。",
        "conclusion": "同一矩阵在 U 上合法，非空性未省略。"
      },
      "dependencies": [
        "CH02-D02",
        "CH02-P05"
      ]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {
          "file": "Chains.lean",
          "name": "LCH02.lip_chain"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.finite_lip_chain"
        }
      ],
      "representation": {
        "objects": "有限族版本使用 φ:Fin n→Operator X bot、M:Fin n→Mat I；每一步都在实际前缀像域上取证书。",
        "parameters": "U⊆dom(c_n)，且每个 m:Fin n 的 M m 是 φ m 在 imageDomain … m 上的 Lip 证书。",
        "quantifiers": "任意长度 n，包含正文全部正长度链；不以全链证书为假设。",
        "conclusion": "由逐步证书归纳构造 matrixProduct 为全复合在 U 上的合法证书。"
      },
      "dependencies": [
        "CH02-D01",
        "CH02-D04",
        "CH02-D05",
        "CH02-P04",
        "CH02-P11"
      ]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        {
          "file": "Chains.lean",
          "name": "LCH02.colip_chain"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.colip_chain_positive"
        },
        {
          "file": "Chains.lean",
          "name": "LCH02.finite_colip_chain"
        }
      ],
      "representation": {
        "objects": "同样使用实际前缀像域；正长度版本从第零步的证书取得起始域非空性。",
        "parameters": "0<n、U⊆dom(c_n)，每个 m:Fin n 给定实际输入域上的 co-Lip 证书。",
        "quantifiers": "任意正长度和所有单步证书；不预设全链证书。",
        "conclusion": "归纳得有序连乘为全复合的 co-Lip 证书，并保留起始域非空性。"
      },
      "dependencies": [
        "CH02-D02",
        "CH02-D04",
        "CH02-D05",
        "CH02-P08",
        "CH02-P12"
      ]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {
          "file": "Paths.lean",
          "name": "LCH02.product_zero_iff"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.product_zero_vertices_iff"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.finite_product_zero_vertices_iff"
        },
        {
          "file": "Paths.lean",
          "name": "LCH02.one_step_zero"
        }
      ],
      "representation": {
        "objects": "最终版本直接量化所有 v:Fin(n+1)→I，并固定 v0=i、vn=j。",
        "parameters": "任意有限 ENNReal 矩阵序列 M:Fin n→Mat I。",
        "quantifiers": "每条固定端点路径都存在 m:Fin n，使该边条目为零；适用所有 n≥1，并额外覆盖 n=0。",
        "conclusion": "有序乘积条目=0 当且仅当每条路径含零因子；one_step_zero 验证 n=1。证明使用 P14 与全正的有限逻辑补集。"
      },
      "dependencies": [
        "CH02-D04",
        "CH02-D06",
        "CH02-P14"
      ]
    }
  ]
}
```
