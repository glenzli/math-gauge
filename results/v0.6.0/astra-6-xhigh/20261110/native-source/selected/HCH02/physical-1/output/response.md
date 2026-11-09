已完成全部 40 项。源码已在 Lean 4.29.1 与指定 mathlib 提交下逐文件编译通过；105 个声明的公理依赖均未超出 `propext`、`Classical.choice`、`Quot.sound`。两份冻结前置模块保持原样。

不依赖规范空间公理的代数引理采用更一般的陈述；实际定义域、co-Lip 非空性和全部点对量词均保留。以下为全部新增项目文件。

```toml filename=lakefile.toml
name = "hch02"
version = "0.1.0"
defaultTargets = ["HCH02"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "HCH02"
roots = ["Main", "Bounds", "Chains", "Paths", "Scalar", "formal_oet.vol_01.ch_01_foundations.gauge_space", "formal_oet.vol_01.ch_01_foundations.operator_space"]
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```lean filename=Main.lean
import Bounds
import Chains
import Paths
import Scalar
```

```lean filename=Bounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic

/- Based on the frozen chapter of The Operator Evolution Theory,
   Zhe Li / Glen Li / glenzli, https://glenzli.com/books/oet/, CC BY 4.0.
   This file is a new Lean formalization of that historical text. -/
noncomputable section
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
open formal_oet.vol_01.ch_01_foundations

namespace HCH02

abbrev Mat (I : Type) := I → I → ENNReal

variable {X I : Type} [Fintype I] {bot : X}

def display (M : Mat I) : Matrix I I ENNReal := fun j i => M i j

theorem display_injective : Function.Injective (display : Mat I → Matrix I I ENNReal) := by
  intro A B h
  funext i j
  exact congrFun (congrFun h j) i

def mmul (B A : Mat I) : Mat I := fun i j => ∑ k, B k j * A i k

theorem display_mmul (B A : Mat I) : display (mmul B A) = display B * display A := rfl

def eye : Mat I := fun i j => if i = j then 1 else 0

theorem display_eye : display (eye : Mat I) = 1 := by
  ext j i
  simp [display, eye, Matrix.one_apply, eq_comm]

def act (M : Mat I) (v : I → ENNReal) (j : I) : ENNReal := ∑ i, M i j * v i

@[simp] theorem act_eye (v : I → ENNReal) (j : I) : act eye v j = v j := by
  classical
  simp [act, eye]

@[simp] theorem mmul_eye (A : Mat I) : mmul A eye = A := by
  classical
  funext i j
  simp [mmul, eye]

@[simp] theorem eye_mmul (A : Mat I) : mmul eye A = A := by
  classical
  funext i j
  simp [mmul, eye]

theorem act_mmul (B A : Mat I) (v : I → ENNReal) (j : I) :
    act (mmul B A) v j = act B (fun k => act A v k) j := by
  simp only [act, mmul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

def product : List (Mat I) → Mat I
  | [] => eye
  | A :: As => mmul (product As) A

@[simp] theorem product_nil : product ([] : List (Mat I)) = eye := rfl
@[simp] theorem product_cons (A : Mat I) (As : List (Mat I)) :
    product (A :: As) = mmul (product As) A := rfl
@[simp] theorem product_singleton (A : Mat I) : product [A] = A := eye_mmul A

theorem display_product (As : List (Mat I)) :
    display (product As) = (As.map display).reverse.prod := by
  induction As with
  | nil => simpa using (display_eye (I := I))
  | cons A As ih => simp [display_mmul, ih]

def ident : Operator X bot := ⟨id, rfl⟩

def comp (ψ φ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ φ.func, by simp [φ.preserves_bot, ψ.preserves_bot]⟩

theorem dom_comp (ψ φ : Operator X bot) :
    dom (comp ψ φ) = {x | x ∈ dom φ ∧ φ.func x ∈ dom ψ} := by
  ext x
  change ψ.func (φ.func x) ≠ bot ↔ φ.func x ≠ bot ∧ ψ.func (φ.func x) ≠ bot
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro hx
    exact h (by rw [hx, ψ.preserves_bot])
  · exact And.right

def Lip (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {L | U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ act L (fun i => d i x y) j}

def GlobalLip (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  Lip d φ (dom φ)

def CoLip (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {K | U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    act K (fun i => d i x y) j ≤ d j (φ.func x) (φ.func y)}

variable {d : I → X → X → ENNReal} {φ ψ : Operator X bot}
  {U V : Set X} {L K : Mat I} {x y : X} {i j : I}

theorem mem_globalLip_iff : L ∈ GlobalLip d φ ↔
    ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j,
      d j (φ.func x) (φ.func y) ≤ ∑ i, L i j * d i x y :=
  ⟨fun h => h.2, fun h => ⟨Set.Subset.rfl, h⟩⟩

theorem lip_restrict (h : L ∈ Lip d φ V) (hUV : U ⊆ V) : L ∈ Lip d φ U :=
  ⟨hUV.trans h.1, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem global_restrict (hU : U ⊆ dom φ) : GlobalLip d φ ⊆ Lip d φ U :=
  fun _ h => lip_restrict h hU

theorem lip_family_antitone (hUV : U ⊆ V) : Lip d φ V ⊆ Lip d φ U :=
  fun _ h => lip_restrict h hUV

def entryInf (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i j : I) : ENNReal := sInf ((fun M : Mat I => M i j) '' Lip d φ U)

theorem entryInf_mono (hUV : U ⊆ V) : entryInf d φ U i j ≤ entryInf d φ V i j := by
  apply sInf_le_sInf
  exact Set.image_mono (lip_family_antitone hUV)

theorem lip_singleton [Unique I] (h : L ∈ Lip d φ U) (hx : x ∈ U) (hy : y ∈ U) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  simpa [act, Subsingleton.elim (default : I) i] using h.2 x hx y hy i

theorem lip_one_component (hi : ∀ k : I, k = i) (h : L ∈ Lip d φ U)
    (hx : x ∈ U) (hy : y ∈ U) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have he : act L (fun k => d k x y) i = L i i * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      exact (hki (hi k)).elim
    · simp
  exact he ▸ h.2 x hx y hy i

theorem lip_comp {A B : Mat I} (hU : U ⊆ dom (comp ψ φ))
    (hA : A ∈ Lip d φ U) (hB : B ∈ Lip d ψ (φ.func '' U)) :
    mmul B A ∈ Lip d (comp ψ φ) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (ψ.func (φ.func x)) (ψ.func (φ.func y)) ≤ _
  rw [act_mmul]
  apply (hB.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j).trans
  exact Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2 x hx y hy k) (B k j)

theorem colip_comp {A B : Mat I} (hU : U ⊆ dom (comp ψ φ))
    (hA : A ∈ CoLip d φ U) (hB : B ∈ CoLip d ψ (φ.func '' U)) :
    mmul B A ∈ CoLip d (comp ψ φ) U := by
  refine ⟨hA.1, hU, ?_⟩
  intro x hx y hy j
  rw [act_mmul]
  apply le_trans _ (hB.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)
  exact Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2.2 x hx y hy k) (B k j)

theorem colip_term (h : K ∈ CoLip d φ U) (hx : x ∈ U) (hy : y ∈ U) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) :=
  (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)).trans
    (h.2.2 x hx y hy j)

theorem colip_zero (h : K ∈ CoLip d φ (dom φ)) (hx : x ∈ dom φ) (hy : y ∈ dom φ)
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K i j = 0 := by
  have hz : K i j * d i x y = 0 := le_antisymm (hout ▸ colip_term h hx hy) (zero_le _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hin)

theorem lip_ident (hU : U ⊆ dom (ident : Operator X bot)) :
    eye ∈ Lip d (ident : Operator X bot) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simp [ident]

theorem colip_ident (hne : U.Nonempty) (hU : U ⊆ dom (ident : Operator X bot)) :
    eye ∈ CoLip d (ident : Operator X bot) U := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  simp [ident]

def Channel (I : Type) := I × I
def Row (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0
def Col (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ j → L i k = 0
def Diagonal (L : Mat I) : Prop := ∀ i j, i ≠ j → L i j = 0
def RowDecoupled (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (j : I) :
    Prop := ∃ L ∈ Lip d φ U, ∃ i, Row L i j
def ColDecoupled (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i : I) :
    Prop := ∃ L ∈ Lip d φ U, ∃ j, Col L i j

theorem zero_term (h : L i j = 0) : L i j * d i x y = 0 := by rw [h, zero_mul]

theorem erase_zero_term (h : L i j = 0) :
    act L (fun k => d k x y) j = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  classical
  simpa [h, act] using (Finset.sum_erase_add (s := Finset.univ)
    (f := fun k => L k j * d k x y) (Finset.mem_univ i)).symm

theorem row_sum (h : Row L i j) (v : I → ENNReal) : act L v j = L i j * v i := by
  classical
  apply Finset.sum_eq_single i
  · intro k hk hki
    rw [h k hki, zero_mul]
  · simp

theorem row_bound (hL : L ∈ Lip d φ U) (h : Row L i j) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  simpa [row_sum h] using hL.2 x hx y hy j

theorem col_contribution (h : Col L i j) {k : I} (hk : k ≠ j) :
    L i k * d i x y = 0 := zero_term (h k hk)

theorem diagonal_bound (hL : L ∈ Lip d φ U) (h : Diagonal L)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  row_bound hL (fun k hk => h k j hk) hx hy

theorem scalar_sandwich (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    (h : Row L j j) (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  ⟨colip_term hK hx hy, row_bound hL h hx hy⟩

theorem diagonal_sandwich (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    (h : Diagonal L) : ∀ j, ∀ x ∈ U, ∀ y ∈ U,
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j _ hx _ hy => scalar_sandwich hL hK (fun k hk => h k j hk) hx hy

theorem finite_diagonal_sandwich (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    (h : Diagonal L) (hf : ∀ j, L j j < ⊤ ∧ K j j < ⊤) : ∀ j,
    L j j < ⊤ ∧ K j j < ⊤ ∧ ∀ x ∈ U, ∀ y ∈ U,
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j => ⟨(hf j).1, (hf j).2, diagonal_sandwich hL hK h j⟩

theorem positive_channel (hK : K ∈ CoLip d φ U) (h : 0 < K i j)
    (hx : x ∈ U) (hy : y ∈ U) (hxy : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) := by
  have hp : 0 < K i j * d i x y := by positivity
  exact hp.trans_le (colip_term hK hx hy)

theorem reflects_zero (hK : K ∈ CoLip d φ U) (h : ∀ j, 0 < K j j)
    (hx : x ∈ U) (hy : y ∈ U) (hout : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra hn
  have hp := positive_channel hK (h j) hx hy (pos_iff_ne_zero.mpr hn)
  rw [hout j] at hp
  exact (lt_irrefl 0) hp

theorem perturb_forward (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ d j (φ.func x) (φ.func y) + δ j + δ j := by
  calc
    _ ≤ d j (ψ.func x) (φ.func x) +
        (d j (φ.func x) (φ.func y) + d j (φ.func y) (ψ.func y)) :=
      ((hd j).triangle _ _ _).trans (add_le_add le_rfl ((hd j).triangle _ _ _))
    _ ≤ δ j + (d j (φ.func x) (φ.func y) + δ j) := by
      apply add_le_add
      · rw [(hd j).symm]
        exact hδ x hx j
      · exact add_le_add le_rfl (hδ y hy j)
    _ = _ := by simp only [add_comm]

theorem perturb_reverse (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ d j (ψ.func x) (ψ.func y) + δ j + δ j := by
  apply perturb_forward hd (φ := ψ) (ψ := φ) _ hx hy j
  intro z hz j
  rw [(hd j).symm]
  exact hδ z hz j

theorem perturb_lip (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hL : L ∈ Lip d φ U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ act L (fun i => d i x y) j + 2 * δ j := by
  calc
    _ ≤ d j (φ.func x) (φ.func y) + δ j + δ j := perturb_forward hd hδ hx hy j
    _ ≤ act L (fun i => d i x y) j + δ j + δ j :=
      add_le_add (add_le_add (hL.2 x hx y hy j) le_rfl) le_rfl
    _ = _ := by rw [two_mul, add_assoc]

theorem perturb_colip (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hK : K ∈ CoLip d φ U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    act K (fun i => d i x y) j ≤ d j (ψ.func x) (ψ.func y) + 2 * δ j := by
  simpa only [two_mul, add_assoc] using (hK.2.2 x hx y hy j).trans
    (perturb_reverse hd hδ hx hy j)

end HCH02
```

```lean filename=Chains.lean
import Bounds

noncomputable section
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
open formal_oet.vol_01.ch_01_foundations
namespace HCH02
variable {X I : Type} [Fintype I] {bot : X}

abbrev Step (X I : Type) (bot : X) := Operator X bot × Mat I

def run : List (Step X I bot) → Operator X bot
  | [] => ident
  | p :: ps => comp (run ps) p.1

def stage : List (Step X I bot) → Set X → ℕ → Set X
  | _, U, 0 => U
  | [], U, _ + 1 => U
  | p :: ps, U, m + 1 => stage ps (p.1.func '' U) m

theorem stage_succ (ps : List (Step X I bot)) (U : Set X) (m : ℕ) (hm : m < ps.length) :
    stage ps U (m + 1) = (ps[m]).1.func '' stage ps U m := by
  induction ps generalizing U m with
  | nil => simp at hm
  | cons p ps ih =>
    cases m with
    | zero => simp [stage]
    | succ m => simpa [stage] using ih (p.1.func '' U) m (by simpa using hm)

theorem stage_eq_image_take (ps : List (Step X I bot)) (U : Set X) (m : ℕ) :
    stage ps U m = (run (ps.take m)).func '' U := by
  induction ps generalizing U m with
  | nil => cases m <;> simp [stage, run, ident]
  | cons p ps ih =>
    cases m with
    | zero => simp [stage, run, ident]
    | succ m => simpa [stage, run, comp, Set.image_image] using ih (p.1.func '' U) m

theorem final_image (ps : List (Step X I bot)) (U : Set X) :
    stage ps U ps.length = (run ps).func '' U := by
  rw [stage_eq_image_take, List.take_length]

theorem run_domain_split (p : Step X I bot) (ps : List (Step X I bot)) {U : Set X}
    (hU : U ⊆ dom (run (p :: ps))) :
    U ⊆ dom p.1 ∧ p.1.func '' U ⊆ dom (run ps) := by
  simp only [run, dom_comp, Set.subset_def, Set.mem_setOf_eq] at hU
  refine ⟨fun x hx => (hU x hx).1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (hU x hx).2

theorem stage_domain (ps : List (Step X I bot)) {U : Set X}
    (hU : U ⊆ dom (run ps)) :
    ∀ m (hm : m < ps.length), stage ps U m ⊆ dom (ps[m]).1 := by
  induction ps generalizing U with
  | nil => simp
  | cons p ps ih =>
    have hs := run_domain_split p ps hU
    intro m hm
    cases m with
    | zero => simpa [stage] using hs.1
    | succ m => simpa [stage] using ih hs.2 m (by simpa using hm)

def AllSteps (P : Operator X bot → Mat I → Set X → Prop) :
    List (Step X I bot) → Set X → Prop
  | [], _ => True
  | p :: ps, U => P p.1 p.2 U ∧ AllSteps P ps (p.1.func '' U)

theorem allSteps_iff (P : Operator X bot → Mat I → Set X → Prop)
    (ps : List (Step X I bot)) (U : Set X) :
    AllSteps P ps U ↔ ∀ m (hm : m < ps.length), P (ps[m]).1 (ps[m]).2 (stage ps U m) := by
  induction ps generalizing U with
  | nil => simp [AllSteps]
  | cons p ps ih =>
    rw [AllSteps, ih]
    constructor
    · rintro ⟨h, hs⟩ m hm
      cases m with
      | zero => simpa [stage] using h
      | succ m => simpa [stage] using hs m (by simpa using hm)
    · intro h
      constructor
      · simpa [stage] using h 0 (by simp)
      · intro m hm
        simpa [stage] using h (m + 1) (by simpa using hm)

def matrices (ps : List (Step X I bot)) : List (Mat I) := ps.map Prod.snd

theorem chain_lip {d : I → X → X → ENNReal} (ps : List (Step X I bot)) {U : Set X}
    (hU : U ⊆ dom (run ps)) (hs : AllSteps (fun φ M V => M ∈ Lip d φ V) ps U) :
    product (matrices ps) ∈ Lip d (run ps) U := by
  induction ps generalizing U with
  | nil => exact lip_ident hU
  | cons p ps ih =>
    exact lip_comp hU hs.1 (ih (run_domain_split p ps hU).2 hs.2)

theorem chain_colip_aux {d : I → X → X → ENNReal} (ps : List (Step X I bot)) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom (run ps))
    (hs : AllSteps (fun φ M V => M ∈ CoLip d φ V) ps U) :
    product (matrices ps) ∈ CoLip d (run ps) U := by
  induction ps generalizing U with
  | nil => exact colip_ident hne hU
  | cons p ps ih =>
    exact colip_comp hU hs.1
      (ih (hne.image p.1.func) (run_domain_split p ps hU).2 hs.2)

theorem chain_colip {d : I → X → X → ENNReal} (ps : List (Step X I bot)) {U : Set X}
    (hpos : ps ≠ []) (hU : U ⊆ dom (run ps))
    (hs : AllSteps (fun φ M V => M ∈ CoLip d φ V) ps U) :
    product (matrices ps) ∈ CoLip d (run ps) U := by
  cases ps with
  | nil => exact (hpos rfl).elim
  | cons p ps => exact chain_colip_aux (p :: ps) hs.1.1 hU hs

theorem chain_lip_from_local {d : I → X → X → ENNReal} (ps : List (Step X I bot))
    {U : Set X} (hU : U ⊆ dom (run ps))
    (hs : ∀ m (hm : m < ps.length), (ps[m]).2 ∈ Lip d (ps[m]).1 (stage ps U m)) :
    product (matrices ps) ∈ Lip d (run ps) U :=
  chain_lip ps hU ((allSteps_iff _ ps U).mpr hs)

theorem chain_colip_from_local {d : I → X → X → ENNReal} (ps : List (Step X I bot))
    {U : Set X} (hpos : ps ≠ []) (hU : U ⊆ dom (run ps))
    (hs : ∀ m (hm : m < ps.length), (ps[m]).2 ∈ CoLip d (ps[m]).1 (stage ps U m)) :
    product (matrices ps) ∈ CoLip d (run ps) U :=
  chain_colip ps hpos hU ((allSteps_iff _ ps U).mpr hs)

end HCH02
```

```lean filename=Paths.lean
import Chains

noncomputable section
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
open formal_oet.vol_01.ch_01_foundations
namespace HCH02
variable {I : Type} [Fintype I]

/- A :: As is in application order. The path contains exactly the
   As.length intermediate indices; its endpoints are the parameters i,j. -/
abbrev Path (I : Type) (n : ℕ) := Fin n → I

def weight (A : Mat I) : (As : List (Mat I)) → I → I → Path I As.length → ENNReal
  | [], i, j, _ => A i j
  | B :: Bs, i, j, p => weight B Bs (p 0) j (fun k => p k.succ) * A i (p 0)

def AllPositive (A : Mat I) : (As : List (Mat I)) → I → I → Path I As.length → Prop
  | [], i, j, _ => 0 < A i j
  | B :: Bs, i, j, p => 0 < A i (p 0) ∧ AllPositive B Bs (p 0) j (fun k => p k.succ)

def HasZero (A : Mat I) : (As : List (Mat I)) → I → I → Path I As.length → Prop
  | [], i, j, _ => A i j = 0
  | B :: Bs, i, j, p => A i (p 0) = 0 ∨ HasZero B Bs (p 0) j (fun k => p k.succ)

def emptyPath : Path I 0 := Fin.elim0

theorem emptyPath_unique (p : Path I 0) : p = emptyPath := by
  funext k
  exact Fin.elim0 k

theorem weight_singleton (A : Mat I) (i j : I) (p : Path I 0) :
    weight A [] i j p = A i j := rfl

theorem weight_zero (A : Mat I) (As : List (Mat I)) (i j : I) (p : Path I As.length) :
    weight A As i j p = 0 ↔ HasZero A As i j p := by
  induction As generalizing A i with
  | nil => rfl
  | cons B Bs ih => simp only [weight, HasZero, mul_eq_zero, ih, or_comm]

theorem weight_positive (A : Mat I) (As : List (Mat I)) (i j : I) (p : Path I As.length) :
    0 < weight A As i j p ↔ AllPositive A As i j p := by
  induction As generalizing A i with
  | nil => rfl
  | cons B Bs ih => simp only [weight, AllPositive, ENNReal.mul_pos_iff, ih, and_comm]

theorem product_expansion (A : Mat I) (As : List (Mat I)) (i j : I) :
    product (A :: As) i j = ∑ p : Path I As.length, weight A As i j p := by
  induction As generalizing A i with
  | nil => simp [weight, Path]
  | cons B Bs ih =>
    change (∑ k, product (B :: Bs) k j * A i k) = _
    simp_rw [ih, Finset.sum_mul]
    rw [← Fintype.sum_prod_type
      (fun q : I × Path I Bs.length => weight B Bs q.1 j q.2 * A i q.1)]
    exact Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (Bs.length + 1) => I))
      _ _ (fun _ => rfl)

theorem product_zero_iff (A : Mat I) (As : List (Mat I)) (i j : I) :
    product (A :: As) i j = 0 ↔ ∀ p : Path I As.length, HasZero A As i j p := by
  rw [product_expansion]
  simp only [Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const, weight_zero]

theorem product_positive_iff (A : Mat I) (As : List (Mat I)) (i j : I) :
    0 < product (A :: As) i j ↔ ∃ p : Path I As.length, AllPositive A As i j p := by
  rw [product_expansion]
  simp only [Finset.sum_pos_iff, Finset.mem_univ, true_and, weight_positive]

theorem singleton_criteria (A : Mat I) (i j : I) :
    ((∀ p : Path I 0, HasZero A [] i j p) ↔ A i j = 0) ∧
    ((∃ p : Path I 0, AllPositive A [] i j p) ↔ 0 < A i j) := by
  simp [HasZero, AllPositive, Path]

/- These specializations retain the original actual-domain certificate
   hypotheses. The algebraic lemmas above need no metric assumptions. -/
theorem lip_chain_zero_iff {X : Type} {bot : X} {d : I → X → X → ENNReal}
    (p : Step X I bot) (ps : List (Step X I bot)) {U : Set X}
    (hU : U ⊆ dom (run (p :: ps)))
    (hs : AllSteps (fun φ M V => M ∈ Lip d φ V) (p :: ps) U) (i j : I) :
    product (matrices (p :: ps)) ∈ Lip d (run (p :: ps)) U ∧
    (product (matrices (p :: ps)) i j = 0 ↔
      ∀ q : Path I (matrices ps).length, HasZero p.2 (matrices ps) i j q) :=
  ⟨chain_lip (p :: ps) hU hs, product_zero_iff p.2 (matrices ps) i j⟩

theorem colip_chain_positive_iff {X : Type} {bot : X} {d : I → X → X → ENNReal}
    (p : Step X I bot) (ps : List (Step X I bot)) {U : Set X}
    (hU : U ⊆ dom (run (p :: ps)))
    (hs : AllSteps (fun φ M V => M ∈ CoLip d φ V) (p :: ps) U) (i j : I) :
    product (matrices (p :: ps)) ∈ CoLip d (run (p :: ps)) U ∧
    (0 < product (matrices (p :: ps)) i j ↔
      ∃ q : Path I (matrices ps).length, AllPositive p.2 (matrices ps) i j q) :=
  ⟨chain_colip (p :: ps) (by simp) hU hs,
    product_positive_iff p.2 (matrices ps) i j⟩

end HCH02
```

```lean filename=Scalar.lean
import Bounds
import Mathlib.Data.ENNReal.Inv

noncomputable section
open scoped Classical
open formal_oet.vol_01.ch_01_foundations
namespace HCH02
variable {X I : Type} {bot : X}

def ScalarSet (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (i j : I) : Set ENNReal :=
  {a | ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ a * d i x y}

def channelInf (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (i j : I) : ENNReal := sInf (ScalarSet d φ U i j)

variable {d : I → X → X → ENNReal} {φ : Operator X bot} {U : Set X} {i j : I}
  {a b : ENNReal}

theorem scalar_upward (ha : a ∈ ScalarSet d φ U i j) (hab : a ≤ b) :
    b ∈ ScalarSet d φ U i j :=
  fun x hx y hy => (ha x hx y hy).trans (mul_le_mul_left hab _)

theorem above_inf_feasible (h : channelInf d φ U i j < b) : b ∈ ScalarSet d φ U i j := by
  obtain ⟨a, ha, hab⟩ := sInf_lt_iff.mp h
  exact scalar_upward ha hab.le

theorem zero_inf_positive (h : channelInf d φ U i j = 0) (hb : 0 < b) :
    b ∈ ScalarSet d φ U i j := above_inf_feasible (h ▸ hb)

theorem finite_inf_iff : channelInf d φ U i j < ⊤ ↔
    ∃ a < ⊤, a ∈ ScalarSet d φ U i j := by
  constructor
  · intro h
    obtain ⟨a, ha, hat⟩ := sInf_lt_iff.mp h
    exact ⟨a, hat, ha⟩
  · rintro ⟨a, hat, ha⟩
    exact (sInf_le ha).trans_lt hat

theorem scalar_empty_of_zero_input {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (φ.func x) (φ.func y)) :
    ScalarSet d φ U i j = ∅ ∧ channelInf d φ U i j = ⊤ := by
  have he : ScalarSet d φ U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have h := ha x hx y hy
    rw [hin, mul_zero] at h
    exact (not_le_of_gt hout) h
  exact ⟨he, by simp [channelInf, he]⟩

theorem positive_finite_inf_attained (hpos : 0 < channelInf d φ U i j)
    (hfin : channelInf d φ U i j < ⊤) :
    channelInf d φ U i j ∈ ScalarSet d φ U i j := by
  intro x hx y hy
  by_cases hzero : d i x y = 0
  · obtain ⟨b, hb, _⟩ := sInf_lt_iff.mp hfin
    simpa [hzero] using hb x hx y hy
  · by_cases htop : d i x y = ⊤
    · rw [htop, ENNReal.mul_top (ne_of_gt hpos)]
      exact le_top
    · change d j (φ.func x) (φ.func y) ≤ sInf (ScalarSet d φ U i j) * d i x y
      rw [sInf_eq_iInf, ENNReal.iInf_mul_of_ne hzero htop]
      apply le_iInf
      intro b
      rw [ENNReal.iInf_mul_of_ne hzero htop]
      exact le_iInf fun hb => hb x hx y hy

/- A genuine gauge-space counterexample: component false has infinite
   distance between distinct points; component true has distance one
   between the two nonabsorbing points. -/
def counterDist (j : Bool) (x y : Fin 3) : ENNReal :=
  if x = y then 0 else if x = 0 ∨ y = 0 then ⊤ else if j then 1 else ⊤

theorem counterMetric (j : Bool) : ExtendedPseudoMetric (Fin 3) 0 (counterDist j) := by
  refine ⟨⟨1, by decide⟩, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [counterDist]
  · intro x y
    simp only [counterDist, eq_comm, or_comm]
  · intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> cases j <;>
      norm_num [counterDist]
  · intro x hx
    simp [counterDist, hx]

def counterU : Set (Fin 3) := {x | x ≠ 0}

theorem counter_domain : counterU.Nonempty ∧ counterU ⊆ dom (ident : Operator (Fin 3) 0) := by
  exact ⟨⟨1, by change (1 : Fin 3) ≠ 0; decide⟩, fun _ hx => hx⟩

theorem counter_positive_feasible (a : ENNReal) (ha : 0 < a) :
    a ∈ ScalarSet counterDist (ident : Operator (Fin 3) 0) counterU false true := by
  intro x hx y hy
  change x ≠ 0 at hx
  change y ≠ 0 at hy
  by_cases hxy : x = y
  · simp [ident, counterDist, hxy]
  · simp [ident, counterDist, hxy, hx, hy, ENNReal.mul_top (ne_of_gt ha)]

theorem counter_inf_zero :
    channelInf counterDist (ident : Operator (Fin 3) 0) counterU false true = 0 := by
  apply le_antisymm _ (zero_le _)
  apply le_of_forall_gt
  intro b hb
  obtain ⟨a, ha, hab⟩ := exists_between hb
  exact (sInf_le (counter_positive_feasible a ha)).trans_lt hab

theorem counter_zero_not_feasible :
    0 ∉ ScalarSet counterDist (ident : Operator (Fin 3) 0) counterU false true := by
  intro h
  have h12 := h 1 (by change (1 : Fin 3) ≠ 0; decide)
    2 (by change (2 : Fin 3) ≠ 0; decide)
  norm_num [ident, counterDist, show (1 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide] at h12

theorem zero_inf_counterexample :
    (∀ j : Bool, ExtendedPseudoMetric (Fin 3) 0 (counterDist j)) ∧
    counterU.Nonempty ∧ counterU ⊆ dom (ident : Operator (Fin 3) 0) ∧
    channelInf counterDist (ident : Operator (Fin 3) 0) counterU false true = 0 ∧
    0 ∉ ScalarSet counterDist (ident : Operator (Fin 3) 0) counterU false true :=
  ⟨counterMetric, counter_domain.1, counter_domain.2, counter_inf_zero, counter_zero_not_feasible⟩

end HCH02
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
        {"file": "Bounds.lean", "name": "HCH02.Lip"},
        {"file": "Bounds.lean", "name": "HCH02.GlobalLip"},
        {"file": "Bounds.lean", "name": "HCH02.mem_globalLip_iff"}
      ],
      "representation": "Lip是含U⊆dom φ和全部点对、全部输出分量求和不等式的矩阵集合；GlobalLip取U=dom φ，并证明与正文全域公式等价。系数和距离均为ENNReal。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D02",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.CoLip"}
      ],
      "representation": "CoLip显式包含U.Nonempty、U⊆dom φ及全部点对、全部输出分量的求和下界；未对0或∞系数作限制。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D03",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.Mat"},
        {"file": "Bounds.lean", "name": "HCH02.display"},
        {"file": "Bounds.lean", "name": "HCH02.display_injective"},
        {"file": "Bounds.lean", "name": "HCH02.mmul"},
        {"file": "Bounds.lean", "name": "HCH02.display_mmul"},
        {"file": "Bounds.lean", "name": "HCH02.act"}
      ],
      "representation": "M i j按输入i、输出j存储；display M j i=M i j，映射单射；证明display(mmul B A)=display B*display A，内部系数为Σk B k j*A i k。",
      "dependencies": []
    },
    {
      "id": "HC02-D04",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.eye"},
        {"file": "Bounds.lean", "name": "HCH02.product"},
        {"file": "Bounds.lean", "name": "HCH02.product_nil"},
        {"file": "Bounds.lean", "name": "HCH02.product_cons"},
        {"file": "Bounds.lean", "name": "HCH02.product_singleton"},
        {"file": "Bounds.lean", "name": "HCH02.display_eye"},
        {"file": "Bounds.lean", "name": "HCH02.display_product"}
      ],
      "representation": "eye为Kronecker单位；product按施行顺序列表递归，空列为单位、单元素为该矩阵；display_product证明其等于反序列表的通常矩阵乘积。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D05",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.Step"},
        {"file": "Chains.lean", "name": "HCH02.run"},
        {"file": "Chains.lean", "name": "HCH02.stage"},
        {"file": "Chains.lean", "name": "HCH02.stage_succ"},
        {"file": "Chains.lean", "name": "HCH02.stage_domain"},
        {"file": "Chains.lean", "name": "HCH02.final_image"},
        {"file": "Chains.lean", "name": "HCH02.AllSteps"},
        {"file": "Chains.lean", "name": "HCH02.allSteps_iff"}
      ],
      "representation": "列表元素仅是算子和单步矩阵。stage ps U m对应U_(m+1)；证明逐次像递推、每一步实际域合法及最终像等式。AllSteps仅要求各步局部界，allSteps_iff证明其与原文逐步索引数据等价，无最终复合界字段。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D06",
      "status": "complete",
      "declarations": [
        {"file": "Paths.lean", "name": "HCH02.Path"},
        {"file": "Paths.lean", "name": "HCH02.weight"},
        {"file": "Paths.lean", "name": "HCH02.AllPositive"},
        {"file": "Paths.lean", "name": "HCH02.HasZero"},
        {"file": "Paths.lean", "name": "HCH02.emptyPath_unique"},
        {"file": "Paths.lean", "name": "HCH02.weight_singleton"},
        {"file": "Paths.lean", "name": "HCH02.weight_zero"},
        {"file": "Paths.lean", "name": "HCH02.weight_positive"}
      ],
      "representation": "长度n≥1的矩阵列写作A::As，Path I As.length=Fin(n-1)→I遍历全部中间序列，不附加正性限制。端点i,j为参数，weight递归乘全部边；全正和含零谓词逐边递归，证明其分别等价于权重正和权重零。一步链的中间序列唯一。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-D07",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.Channel"},
        {"file": "Bounds.lean", "name": "HCH02.Row"},
        {"file": "Bounds.lean", "name": "HCH02.Col"},
        {"file": "Bounds.lean", "name": "HCH02.Diagonal"},
        {"file": "Bounds.lean", "name": "HCH02.RowDecoupled"},
        {"file": "Bounds.lean", "name": "HCH02.ColDecoupled"}
      ],
      "representation": "Channel=I×I；Row固定输出j且仅输入i可能非零，Col固定输入i且仅输出j可能非零；行、列解耦对合法Lip证书及支撑位置作存在量化；Diagonal要求所有非对角系数为零。",
      "dependencies": ["HC02-D01", "HC02-D03"]
    },
    {
      "id": "HC02-D08",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.ScalarSet"},
        {"file": "Scalar.lean", "name": "HCH02.channelInf"}
      ],
      "representation": "ScalarSet是全部点对的单输入分量标量可行集合，channelInf为其ENNReal下确界，空集下确界为∞。这两个对象与矩阵条目下确界entryInf分别定义。",
      "dependencies": []
    },
    {
      "id": "HC02-P01",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.lip_one_component"}
      ],
      "representation": "以∀k:I,k=i表达I={i}；证明所有作用域点对的输出距≤L i i*d i x y。",
      "dependencies": ["HC02-D01", "HC02-D03"]
    },
    {
      "id": "HC02-P02",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.global_restrict"}
      ],
      "representation": "U⊆dom φ时，全域Lip矩阵族包含于U上的受限族。",
      "dependencies": ["HC02-D01", "HC02-P03"]
    },
    {
      "id": "HC02-P03",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.lip_restrict"},
        {"file": "Bounds.lean", "name": "HCH02.lip_family_antitone"}
      ],
      "representation": "U⊆V时，每个V上的合法证书限制到U仍合法，从而证书族反向包含；V的定义域合法性由原证书提供。",
      "dependencies": ["HC02-D01"]
    },
    {
      "id": "HC02-P04",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.entryInf"},
        {"file": "Bounds.lean", "name": "HCH02.entryInf_mono"}
      ],
      "representation": "逐条目下确界定义为合法矩阵集合在M↦M i j下的像集的sInf；U⊆V推出U上的下确界≤V上的下确界。",
      "dependencies": ["HC02-D01", "HC02-P03"]
    },
    {
      "id": "HC02-P05",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.lip_comp"}
      ],
      "representation": "在U⊆dom(ψ∘φ)、第一步U上合法、第二步φ(U)上合法的条件下，证明mmul B A是复合在U上的Lip证书。",
      "dependencies": ["HC02-D01", "HC02-D03"]
    },
    {
      "id": "HC02-P06",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.colip_zero"}
      ],
      "representation": "任意全域co-Lip证书、定义域内点对、输入分量正距且输出分量零距，推出相应系数为零。",
      "dependencies": ["HC02-D02", "HC02-D03"]
    },
    {
      "id": "HC02-P07",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.colip_comp"}
      ],
      "representation": "与两步Lip相同的实际像域，证明mmul B A满足复合co-Lip下界并从第一步证书保留U非空性。",
      "dependencies": ["HC02-D02", "HC02-D03"]
    },
    {
      "id": "HC02-P08",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.perturb_forward"}
      ],
      "representation": "对规范族、全部z∈U及j的逐点δ界，证明ψ的点对像距≤φ的点对像距+δj+δj。证明对任意U成立，故包含原文公共定义域内的情形。",
      "dependencies": []
    },
    {
      "id": "HC02-P09",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.perturb_reverse"}
      ],
      "representation": "由同一逐点扰动前提和距离对称性得到反向点对扰动界。",
      "dependencies": ["HC02-P08"]
    },
    {
      "id": "HC02-P10",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.perturb_lip"}
      ],
      "representation": "代入φ在U上的Lip证书，得到ψ的输出距≤矩阵作用于输入距离的和+2*δj；交换算子可再次实例化同一声明。",
      "dependencies": ["HC02-D01", "HC02-P08"]
    },
    {
      "id": "HC02-P11",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.perturb_colip"}
      ],
      "representation": "代入φ在U上的co-Lip证书，得到矩阵输入距离和≤ψ的输出距+2*δj；交换算子同样适用。",
      "dependencies": ["HC02-D02", "HC02-P09"]
    },
    {
      "id": "HC02-P12",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.chain_lip"},
        {"file": "Chains.lean", "name": "HCH02.chain_lip_from_local"}
      ],
      "representation": "对任意按施行顺序的有限列表，从每个实际stage域上的指定单步Lip证书归纳推出指定有序乘积的复合界；索引版本直接接收各步原文数据，并包含所有正长度。",
      "dependencies": ["HC02-D01", "HC02-D04", "HC02-D05", "HC02-P05", "HC02-P14"]
    },
    {
      "id": "HC02-P13",
      "status": "complete",
      "declarations": [
        {"file": "Chains.lean", "name": "HCH02.chain_colip"},
        {"file": "Chains.lean", "name": "HCH02.chain_colip_from_local"}
      ],
      "representation": "对非空列表，从实际stage域上的co-Lip证书推出指定乘积的复合下界；U非空由第一步证书推出，递推过程中使用真实像集。",
      "dependencies": ["HC02-D02", "HC02-D04", "HC02-D05", "HC02-P07", "HC02-P15"]
    },
    {
      "id": "HC02-P14",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.lip_ident"}
      ],
      "representation": "对U⊆dom id证明单位矩阵Lip证书；该结论对空域也成立，特别覆盖正文非空U。",
      "dependencies": ["HC02-D01", "HC02-D04"]
    },
    {
      "id": "HC02-P15",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.colip_ident"}
      ],
      "representation": "对非空U⊆dom id证明同一单位矩阵的co-Lip证书。",
      "dependencies": ["HC02-D02", "HC02-D04"]
    },
    {
      "id": "HC02-P16",
      "status": "complete",
      "declarations": [
        {"file": "Paths.lean", "name": "HCH02.product_expansion"},
        {"file": "Paths.lean", "name": "HCH02.product_zero_iff"},
        {"file": "Paths.lean", "name": "HCH02.lip_chain_zero_iff"},
        {"file": "Paths.lean", "name": "HCH02.singleton_criteria"}
      ],
      "representation": "证明任意指定矩阵乘积是全部中间序列的权重和，零值当且仅当每条路径含零边；在实际局部Lip链下封装合法性与判据，且一步情形退化为唯一条目为零。另一种下界证书不参与该证明。",
      "dependencies": ["HC02-D03", "HC02-D04", "HC02-D06", "HC02-P12"]
    },
    {
      "id": "HC02-P17",
      "status": "complete",
      "declarations": [
        {"file": "Paths.lean", "name": "HCH02.product_expansion"},
        {"file": "Paths.lean", "name": "HCH02.product_positive_iff"},
        {"file": "Paths.lean", "name": "HCH02.colip_chain_positive_iff"},
        {"file": "Paths.lean", "name": "HCH02.singleton_criteria"}
      ],
      "representation": "由全部路径的有限权重和证明乘积条目正当且仅当存在全正路径；在实际局部co-Lip链下封装合法性与判据，一步情形退化为唯一条目正。另一种上界证书不参与该证明。",
      "dependencies": ["HC02-D03", "HC02-D04", "HC02-D06", "HC02-P13"]
    },
    {
      "id": "HC02-P18",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.scalar_empty_of_zero_input"}
      ],
      "representation": "给定U内零输入距、正输出距点对，证明全部ENNReal常数均不可行，可行集合为空且channelInf=∞。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P19",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.positive_finite_inf_attained"}
      ],
      "representation": "在0<channelInf<∞条件下证明该下确界本身属于完整点对可行集合；按输入距离为0、∞、有限非零分情况，有限分支用合法的乘法与下确界交换。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P20",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.scalar_upward"}
      ],
      "representation": "任意a≤b且a满足全部点对标量界，则b也满足。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P21",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.above_inf_feasible"}
      ],
      "representation": "证明任何严格大于channelInf的ENNReal常数可行，包括∞；此更一般命题覆盖正文正有限下确界条件。",
      "dependencies": ["HC02-D08", "HC02-P20"]
    },
    {
      "id": "HC02-P22",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.zero_inf_positive"}
      ],
      "representation": "channelInf=0时任意正ENNReal常数可行，特别包括所有有限正常数；没有断言0可行。",
      "dependencies": ["HC02-D08", "HC02-P21"]
    },
    {
      "id": "HC02-P23",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.counterDist"},
        {"file": "Scalar.lean", "name": "HCH02.counterMetric"},
        {"file": "Scalar.lean", "name": "HCH02.counterU"},
        {"file": "Scalar.lean", "name": "HCH02.zero_inf_counterexample"}
      ],
      "representation": "X=Fin 3、bot=0、I=Bool；false分量的异点距离为∞，true分量的两个非吸收点距离为1，吸收元隔离。φ=id、U={1,2}；证明全部规范公理、域合法非空、通道下确界为0而0不可行。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P24",
      "status": "complete",
      "declarations": [
        {"file": "Scalar.lean", "name": "HCH02.finite_inf_iff"}
      ],
      "representation": "证明channelInf<∞当且仅当存在有限ENNReal常数满足全部U内点对的单通道上界。",
      "dependencies": ["HC02-D08"]
    },
    {
      "id": "HC02-P25",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.zero_term"},
        {"file": "Bounds.lean", "name": "HCH02.erase_zero_term"}
      ],
      "representation": "零系数与任意ENNReal输入距相乘为零，并证明输出有限和等于删除该输入指标后的和；包括输入距∞。",
      "dependencies": ["HC02-D03"]
    },
    {
      "id": "HC02-P26",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.row_sum"},
        {"file": "Bounds.lean", "name": "HCH02.row_bound"}
      ],
      "representation": "任意输入i与输出j，只要合法Lip矩阵的该输出行除i外全零，即得到L i j*d i的单输入上界，无i=j要求。",
      "dependencies": ["HC02-D01", "HC02-D07"]
    },
    {
      "id": "HC02-P27",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.col_contribution"}
      ],
      "representation": "固定输入i列仅输出j可非零时，对每个k≠j证明L i k*d i x y=0；结论适用于所选合法证书。",
      "dependencies": ["HC02-D07", "HC02-P25"]
    },
    {
      "id": "HC02-P28",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.diagonal_bound"}
      ],
      "representation": "对角合法Lip矩阵在每个j及全部U内点对给出L j j的标量上界。",
      "dependencies": ["HC02-D01", "HC02-D07", "HC02-P26"]
    },
    {
      "id": "HC02-P29",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.scalar_sandwich"}
      ],
      "representation": "只要求Lip的第j行仅有对角输入；co-Lip不要求稀疏，由非负项取单项得到K j j下界，与Lip上界合并。",
      "dependencies": ["HC02-D01", "HC02-D02", "HC02-D07", "HC02-P26"]
    },
    {
      "id": "HC02-P30",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.diagonal_sandwich"},
        {"file": "Bounds.lean", "name": "HCH02.finite_diagonal_sandwich"}
      ],
      "representation": "对全部j同时得到双侧标量界；有限分支显式保留L j j<∞、K j j<∞及全部点对双侧不等式。",
      "dependencies": ["HC02-D01", "HC02-D02", "HC02-D07", "HC02-P29"]
    },
    {
      "id": "HC02-P31",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.colip_term"},
        {"file": "Bounds.lean", "name": "HCH02.positive_channel"}
      ],
      "representation": "从co-Lip总和取通道单项；正系数与正输入距的ENNReal乘积为正，故输出分量距离正。",
      "dependencies": ["HC02-D02", "HC02-D03"]
    },
    {
      "id": "HC02-P32",
      "status": "complete",
      "declarations": [
        {"file": "Bounds.lean", "name": "HCH02.reflects_zero"}
      ],
      "representation": "所有co-Lip对角系数正时，输出族全分量零距推出输入族全分量零距；使用冻结GaugeZeroRelated，不假设族分离或推出点相等。",
      "dependencies": ["HC02-D02", "HC02-P31"]
    }
  ]
}
```

数学来源：Zhe Li（Glen Li / glenzli），[ORCID](https://orcid.org/0009-0006-6536-3453)，[The Operator Evolution Theory](https://glenzli.com/books/oet/)，[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)。上述新增代码是针对所给历史快照的 AI 辅助形式化。

已完整完成并对齐冻结原文及清单规定的全部 40 项义务。未完成范围：无；未确认的数学范围：无。