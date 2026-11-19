已完成冻结第 2 章的 **40/40 项义务**。项目使用 Lean 4.29.1 和 mathlib 提交 `5e932f97dd25535344f80f9dd8da3aab83df0fe6` 离线构建通过。`leanchecker` 已重新检查三个目标模块和 `Main`。清单中的 97 个不同声明均已核对名称和所属文件，对目标模块全部 147 个常量追溯到的公理只有 `propext`、`Classical.choice`、`Quot.sound`。

两份冻结前置源码的 SHA-256 在构建前后一致。完整项目包包含这些前置源码、冻结文本及许可证，下面给出全部新增文件。[下载 HCH02.zip](/private/tmp/math-gauge-astra62-max-20261119/sessions/HCH02/physical-1/output/artifacts/HCH02.zip)

数学原文为 Zhe Li（Glen Li / glenzli）的 *The Operator Evolution Theory*。本项目将第 2 章快照 `2d2f76c8392daf62` 形式化为 Lean 定义与证明。[作品页](https://glenzli.com/books/oet/) · [作者 ORCID](https://orcid.org/0009-0006-6536-3453) · [公开仓库](https://gitlab.com/glenzli/oet-public) · [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)

```lean filename=Main.lean
import Bounds
import Chains
import Channels
```

```lean filename=Bounds.lean
import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/- The Operator Evolution Theory, Zhe Li (Glen Li / glenzli).
   Chapter 2, frozen text 2d2f76c8392daf62. Adapted to Lean under CC BY 4.0. -/
namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal Classical
noncomputable section

variable {X I : Type} {b : X}

structure Gauge (X I : Type) (b : X) [Fintype I] [Nonempty I] where
  d : I → X → X → ℝ≥0∞
  metric : ∀ i, ExtendedPseudoMetric X b (d i)

abbrev Coeff (I : Type) := I → I → ℝ≥0∞

def display (A : Coeff I) : Matrix I I ℝ≥0∞ := fun j i => A i j

theorem display_entry (A : Coeff I) (i j : I) : display A j i = A i j := rfl

variable [Fintype I]

def mul (B A : Coeff I) (i j : I) := ∑ k, B k j * A i k
def act (A : Coeff I) (v : I → ℝ≥0∞) (j : I) := ∑ i, A i j * v i

theorem display_mul (B A : Coeff I) : display (mul B A) = display B * display A := rfl

theorem act_mul (B A : Coeff I) (v : I → ℝ≥0∞) :
    act (mul B A) v = act B (act A v) :=
  (Matrix.mulVec_mulVec v (display B) (display A)).symm

theorem act_mono (A : Coeff I) {v w : I → ℝ≥0∞} (h : v ≤ w) : act A v ≤ act A w :=
  fun j => Finset.sum_le_sum fun i _ => mul_le_mul_right (h i) (A i j)

theorem term_le_act (A : Coeff I) (v : I → ℝ≥0∞) (i j : I) :
    A i j * v i ≤ act A v j :=
  Finset.single_le_sum (f := fun k => A k j * v k) (fun _ _ => zero_le _) (Finset.mem_univ i)

theorem top_entry {A : Coeff I} {i j : I} (h : A i j = ⊤) (v : I → ℝ≥0∞) :
    (v i = 0 → A i j * v i = 0) ∧
    (0 < v i → A i j * v i = ⊤ ∧ act A v j = ⊤) := by
  refine ⟨fun hz => by rw [hz, mul_zero], fun hp => ?_⟩
  have he : A i j * v i = ⊤ := by rw [h, ENNReal.top_mul hp.ne']
  exact ⟨he, top_unique (he ▸ term_le_act A v i j)⟩

def unitM (I : Type) : Coeff I := fun i j => if i = j then 1 else 0

omit [Fintype I] in
theorem display_unit : display (unitM I) = (1 : Matrix I I ℝ≥0∞) := by
  ext j i
  simp [display, unitM, Matrix.one_apply, eq_comm]

@[simp] theorem act_unit (v : I → ℝ≥0∞) : act (unitM I) v = v := by
  funext j
  simp [act, unitM, ite_mul]

@[simp] theorem mul_unit (A : Coeff I) : mul A (unitM I) = A := by
  funext i j
  simp [mul, unitM, mul_ite]

def ident (b : X) : Operator X b := ⟨id, rfl⟩
def comp (g f : Operator X b) : Operator X b :=
  ⟨g.func ∘ f.func, by simp [f.preserves_bot, g.preserves_bot]⟩

variable {f g : Operator X b} {U V : Set X}

theorem comp_domain : U ⊆ dom (comp g f) ↔ U ⊆ dom f ∧ f.func '' U ⊆ dom g := by
  constructor
  · intro h
    refine ⟨fun x hx he => h hx ?_, ?_⟩
    · change g.func (f.func x) = b
      rw [he, g.preserves_bot]
    · rintro _ ⟨x, hx, rfl⟩
      exact h hx
  · rintro ⟨_, h⟩ x hx
    exact h ⟨x, hx, rfl⟩

variable [Nonempty I] (G : Gauge X I b)

def vec (x y : X) (i : I) := G.d i x y

def lip (f : Operator X b) (U : Set X) : Set (Coeff I) :=
  {A | U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    vec G (f.func x) (f.func y) ≤ act A (vec G x y)}

def globalLip (f : Operator X b) := lip G f (dom f)

def coLip (f : Operator X b) (U : Set X) : Set (Coeff I) :=
  {A | U.Nonempty ∧ U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    act A (vec G x y) ≤ vec G (f.func x) (f.func y)}

variable {G} {A B : Coeff I} {x y : X} {i j : I}

theorem lip_iff : A ∈ lip G f U ↔ U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U → ∀ j,
    G.d j (f.func x) (f.func y) ≤ ∑ i, A i j * G.d i x y := Iff.rfl

theorem coLip_iff : A ∈ coLip G f U ↔ U.Nonempty ∧ U ⊆ dom f ∧
    ∀ ⦃x y⦄, x ∈ U → y ∈ U → ∀ j,
      (∑ i, A i j * G.d i x y) ≤ G.d j (f.func x) (f.func y) := Iff.rfl

theorem singleton_lip [Subsingleton I] (i : I) :
    A ∈ globalLip G f ↔ ∀ ⦃x y⦄, x ∈ dom f → y ∈ dom f →
      G.d i (f.func x) (f.func y) ≤ A i i * G.d i x y := by
  have e (x y : X) : act A (vec G x y) i = A i i * G.d i x y :=
    Fintype.sum_subsingleton _ i
  constructor
  · intro h x y hx hy
    exact (h.2 hx hy i).trans_eq (e x y)
  · intro h
    refine ⟨Set.Subset.rfl, fun {x y} hx hy j => ?_⟩
    obtain rfl := Subsingleton.elim j i
    exact (h hx hy).trans_eq (e x y).symm

theorem lip_shrink (h : U ⊆ V) : lip G f V ⊆ lip G f U :=
  fun _ hA => ⟨h.trans hA.1, fun {_ _} hx hy => hA.2 (h hx) (h hy)⟩

theorem global_restrict (h : U ⊆ dom f) : globalLip G f ⊆ lip G f U := lip_shrink h

def entryInf (G : Gauge X I b) (f : Operator X b) (U : Set X) (i j : I) :=
  sInf ((fun A : Coeff I => A i j) '' lip G f U)

theorem entryInf_mono (h : U ⊆ V) : entryInf G f U i j ≤ entryInf G f V i j :=
  sInf_le_sInf (Set.image_mono (lip_shrink h))

theorem lip_comp (h : U ⊆ dom (comp g f)) (hA : A ∈ lip G f U)
    (hB : B ∈ lip G g (f.func '' U)) : mul B A ∈ lip G (comp g f) U := by
  refine ⟨h, fun {x y} hx hy => ?_⟩
  rw [act_mul]
  exact (hB.2 ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩).trans (act_mono B (hA.2 hx hy))

theorem co_comp (h : U ⊆ dom (comp g f)) (hA : A ∈ coLip G f U)
    (hB : B ∈ coLip G g (f.func '' U)) : mul B A ∈ coLip G (comp g f) U := by
  refine ⟨hA.1, h, fun {x y} hx hy => ?_⟩
  rw [act_mul]
  exact (act_mono B (hA.2.2 hx hy)).trans (hB.2.2 ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

theorem co_term (hA : A ∈ coLip G f U) (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    A i j * G.d i x y ≤ G.d j (f.func x) (f.func y) :=
  (term_le_act A (vec G x y) i j).trans (hA.2.2 hx hy j)

theorem collapsed_entry (hA : A ∈ coLip G f (dom f)) (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hout : G.d j (f.func x) (f.func y) = 0) (hin : 0 < G.d i x y) : A i j = 0 := by
  have h := co_term hA hx hy i j
  rw [hout, nonpos_iff_eq_zero, mul_eq_zero] at h
  exact h.resolve_right hin.ne'

def CloseOn (G : Gauge X I b) (f g : Operator X b) (U : Set X) (δ : I → ℝ≥0∞) :=
  ∀ z ∈ U, ∀ j, G.d j (f.func z) (g.func z) ≤ δ j

variable {δ : I → ℝ≥0∞}

theorem close_swap (h : CloseOn G f g U δ) : CloseOn G g f U δ := by
  intro z hz j
  rw [(G.metric j).symm]
  exact h z hz j

theorem perturb (_hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    G.d j (g.func x) (g.func y) ≤ G.d j (f.func x) (f.func y) + δ j + δ j := by
  have t := (G.metric j).triangle
  calc
    _ ≤ G.d j (g.func x) (f.func x) + G.d j (f.func x) (g.func y) := t _ _ _
    _ ≤ δ j + (G.d j (f.func x) (f.func y) + δ j) :=
      add_le_add (close_swap h x hx j) ((t _ (f.func y) _).trans (add_le_add le_rfl (h y hy j)))
    _ = _ := by rw [← add_assoc, add_comm (δ j) (G.d j (f.func x) (f.func y))]

theorem perturb_rev (hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    G.d j (f.func x) (f.func y) ≤ G.d j (g.func x) (g.func y) + δ j + δ j :=
  perturb (by rwa [Set.inter_comm]) (close_swap h) hx hy j

theorem lip_bridge (hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hA : A ∈ lip G f U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    G.d j (g.func x) (g.func y) ≤ act A (vec G x y) j + 2 * δ j := by
  rw [two_mul, ← add_assoc]
  exact (perturb hU h hx hy j).trans (add_le_add (add_le_add (hA.2 hx hy j) le_rfl) le_rfl)

theorem co_bridge (hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hA : A ∈ coLip G f U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    act A (vec G x y) j ≤ G.d j (g.func x) (g.func y) + 2 * δ j := by
  rw [two_mul, ← add_assoc]
  exact (hA.2.2 hx hy j).trans (perturb_rev hU h hx hy j)

theorem lip_bridge_rev (hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hA : A ∈ lip G g U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    G.d j (f.func x) (f.func y) ≤ act A (vec G x y) j + 2 * δ j :=
  lip_bridge (by rwa [Set.inter_comm]) (close_swap h) hA hx hy j

theorem co_bridge_rev (hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hA : A ∈ coLip G g U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    act A (vec G x y) j ≤ G.d j (f.func x) (f.func y) + 2 * δ j :=
  co_bridge (by rwa [Set.inter_comm]) (close_swap h) hA hx hy j

end
end HCH02
```

```lean filename=Chains.lean
import Bounds
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal Classical
noncomputable section

variable {X I : Type} {b : X} {n : ℕ}

def run : {n : ℕ} → (Fin n → Operator X b) → Operator X b
  | 0, _ => ident b
  | n+1, f => comp (f (Fin.last n)) (run (Fin.init f))

theorem run_eq_chain (f : Fin n → Operator X b) :
    run f = OperatorChain (List.ofFn f).reverse := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.ofFn_succ_last, List.reverse_append]
    change comp _ (run (Fin.init f)) = comp _ (OperatorChain _)
    rw [ih]
    rfl

def stage (f : Fin n → Operator X b) (U : Set X) (t : Fin (n+1)) : Set X :=
  (run (fun r : Fin t.val => f ⟨r.val, lt_of_lt_of_le r.isLt (Nat.le_of_lt_succ t.isLt)⟩)).func '' U

@[simp] theorem stage_zero (f : Fin n → Operator X b) (U : Set X) : stage f U 0 = U := by
  change id '' U = U
  simp

theorem stage_succ (f : Fin n → Operator X b) (U : Set X) (t : Fin n) :
    stage f U t.succ = (f t).func '' stage f U t.castSucc := by
  unfold stage
  rw [Set.image_image]
  rfl

theorem stage_last (f : Fin n → Operator X b) (U : Set X) :
    stage f U (Fin.last n) = (run f).func '' U := rfl

theorem stages_unique {f : Fin n → Operator X b} {U : Set X} {V : Fin (n+1) → Set X}
    (h0 : V 0 = U) (hs : ∀ m, V m.succ = (f m).func '' V m.castSucc) :
    ∀ t, V t = stage f U t := by
  intro t
  induction t using Fin.induction with
  | zero => simpa using h0
  | succ m ih => rw [hs, ih, stage_succ]

theorem final_image {f : Fin n → Operator X b} {U : Set X} {V : Fin (n+1) → Set X}
    (h0 : V 0 = U) (hs : ∀ m, V m.succ = (f m).func '' V m.castSucc) :
    V (Fin.last n) = (run f).func '' U :=
  (stages_unique h0 hs _).trans (stage_last f U)

theorem stage_domain (f : Fin n → Operator X b) {U : Set X} (h : U ⊆ dom (run f))
    (m : Fin n) : stage f U m.castSucc ⊆ dom (f m) := by
  induction n with
  | zero => exact m.elim0
  | succ n ih =>
    refine Fin.lastCases ?_ (fun k => ?_) m
    · exact (comp_domain.mp h).2
    · exact ih (Fin.init f) (comp_domain.mp h).1 k

variable [Fintype I]

def product : {n : ℕ} → (Fin n → Coeff I) → Coeff I
  | 0, _ => unitM I
  | n+1, A => mul (A (Fin.last n)) (product (Fin.init A))

theorem product_empty (A : Fin 0 → Coeff I) : product A = unitM I := rfl
theorem product_step (A : Fin (n+1) → Coeff I) :
    product A = mul (A (Fin.last n)) (product (Fin.init A)) := rfl
@[simp] theorem product_one (A : Fin 1 → Coeff I) : product A = A 0 := mul_unit _

theorem display_product (A : Fin n → Coeff I) :
    display (product A) = (List.ofFn (fun t => display (A t))).reverse.prod := by
  induction n with
  | zero => exact display_unit
  | succ n ih =>
    rw [List.ofFn_succ_last, List.reverse_append, product_step, display_mul, ih]
    rfl

def OnStages (C : Operator X b → Set X → Set (Coeff I)) (f : Fin n → Operator X b)
    (U : Set X) (A : Fin n → Coeff I) := ∀ m, A m ∈ C (f m) (stage f U m.castSucc)

omit [Fintype I] in
theorem onStages_iff {C : Operator X b → Set X → Set (Coeff I)} {f : Fin n → Operator X b}
    {U : Set X} {V : Fin (n+1) → Set X} {A : Fin n → Coeff I}
    (h0 : V 0 = U) (hs : ∀ m, V m.succ = (f m).func '' V m.castSucc) :
    OnStages C f U A ↔ ∀ m, A m ∈ C (f m) (V m.castSucc) := by
  simp only [OnStages, stages_unique h0 hs]

variable [Nonempty I] {G : Gauge X I b} {U : Set X}

theorem id_lip (h : U ⊆ dom (ident b)) : unitM I ∈ lip G (ident b) U := by
  exact ⟨h, fun {x y} _ _ => by simp [ident]⟩

theorem id_coLip (hne : U.Nonempty) (h : U ⊆ dom (ident b)) : unitM I ∈ coLip G (ident b) U := by
  exact ⟨hne, h, fun {x y} _ _ => by simp [ident]⟩

theorem chain_lip (f : Fin n → Operator X b) (A : Fin n → Coeff I) (h : U ⊆ dom (run f))
    (hs : OnStages (lip G) f U A) : product A ∈ lip G (run f) U := by
  induction n with
  | zero => exact id_lip h
  | succ n ih =>
    exact lip_comp h (ih (Fin.init f) (Fin.init A) (comp_domain.mp h).1
      (fun m => hs m.castSucc)) (hs (Fin.last n))

private theorem chain_lower_aux (hne : U.Nonempty) (f : Fin n → Operator X b)
    (A : Fin n → Coeff I) (h : U ⊆ dom (run f)) (hs : OnStages (coLip G) f U A) :
    product A ∈ coLip G (run f) U := by
  induction n with
  | zero => exact id_coLip hne h
  | succ n ih =>
    exact co_comp h (ih (Fin.init f) (Fin.init A) (comp_domain.mp h).1
      (fun m => hs m.castSucc)) (hs (Fin.last n))

theorem chain_coLip (f : Fin (n+1) → Operator X b) (A : Fin (n+1) → Coeff I)
    (h : U ⊆ dom (run f)) (hs : OnStages (coLip G) f U A) :
    product A ∈ coLip G (run f) U := by
  apply chain_lower_aux _ f A h hs
  simpa using (hs 0).1

abbrev Path (I : Type) (n : ℕ) := Fin n → I

def edge (A : Fin (n+1) → Coeff I) (i j : I) (p : Path I n) (t : Fin (n+1)) :=
  A t (Fin.cons (α := fun _ => I) i p t) (Fin.snoc (α := fun _ => I) p j t)

def weight (A : Fin (n+1) → Coeff I) (i j : I) (p : Path I n) :=
  ∏ t, edge A i j p t

def HasZero (A : Fin (n+1) → Coeff I) (i j : I) (p : Path I n) :=
  ∃ t, edge A i j p t = 0

def AllPositive (A : Fin (n+1) → Coeff I) (i j : I) (p : Path I n) :=
  ∀ t, 0 < edge A i j p t

omit [Fintype I] [Nonempty I] in
theorem one_path (A : Fin 1 → Coeff I) (i j : I) :
    (∃! _ : Path I 0, True) ∧ ∀ p : Path I 0,
      weight A i j p = A 0 i j ∧ (HasZero A i j p ↔ A 0 i j = 0) ∧
      (AllPositive A i j p ↔ 0 < A 0 i j) := by
  refine ⟨⟨Fin.elim0, trivial, fun _ _ => Subsingleton.elim _ _⟩, fun p => ?_⟩
  have hj : Fin.snoc (α := fun _ => I) p j (0 : Fin 1) = j := Fin.snoc_last _ _
  simp [weight, edge, HasZero, AllPositive, hj]

omit [Fintype I] [Nonempty I] in
private theorem weight_snoc (A : Fin (n+2) → Coeff I) (i j k : I) (p : Path I n) :
    weight A i j (Fin.snoc p k) = A (Fin.last (n+1)) k j * weight (Fin.init A) i k p := by
  unfold weight
  rw [Fin.prod_univ_castSucc, mul_comm]
  simp only [edge, Fin.cons_snoc_eq_snoc_cons, Fin.snoc_castSucc, Fin.snoc_last, Fin.init]

omit [Nonempty I] in
theorem sum_paths (A : Fin (n+1) → Coeff I) (i j : I) :
    product A i j = ∑ p : Path I n, weight A i j p := by
  induction n generalizing i j with
  | zero =>
    simp [fun p => ((one_path A i j).2 p).1]
  | succ n ih =>
    let e := Fin.snocEquiv (fun _ : Fin (n+1) => I)
    rw [← e.sum_comp (weight A i j), Fintype.sum_prod_type]
    change (∑ k, A (Fin.last _) k j * product (Fin.init A) i k) =
      ∑ k, ∑ p, weight A i j (Fin.snoc p k)
    simp_rw [weight_snoc, ← Finset.mul_sum, ← ih]

theorem path_criteria (f : Fin (n+1) → Operator X b) (L K : Fin (n+1) → Coeff I)
    (_h : U ⊆ dom (run f)) (_hL : OnStages (lip G) f U L) (_hK : OnStages (coLip G) f U K)
    (i j : I) :
    (product L i j = 0 ↔ ∀ p, HasZero L i j p) ∧
    (0 < product K i j ↔ ∃ p, AllPositive K i j p) := by
  classical
  simp [sum_paths, HasZero, AllPositive, weight, pos_iff_ne_zero,
    Finset.sum_eq_zero_iff, Finset.prod_eq_zero_iff, not_forall]

end
end HCH02
```

```lean filename=Channels.lean
import Bounds
import Mathlib.Data.ENNReal.Inv

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal NNReal Classical
noncomputable section

variable {X I : Type} {b : X} [Fintype I] [Nonempty I]
variable (G : Gauge X I b) (f : Operator X b) (U : Set X)

abbrev Channel (I : Type) := I × I

def feasible (i j : I) : Set ℝ≥0∞ :=
  {c | U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    G.d j (f.func x) (f.func y) ≤ c * G.d i x y}

def best (i j : I) := sInf (feasible G f U i j)

variable {G f U} {i j : I} {x y : X} {a c : ℝ≥0∞}

theorem feasible_iff (hU : U ⊆ dom f) :
    c ∈ feasible G f U i j ↔ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
      G.d j (f.func x) (f.func y) ≤ c * G.d i x y :=
  ⟨And.right, fun h => ⟨hU, h⟩⟩

theorem best_empty (h : feasible G f U i j = ∅) : best G f U i j = ⊤ := by
  simp [best, h]

theorem empty_channel (hx : x ∈ U) (hy : y ∈ U) (hz : G.d i x y = 0)
    (hp : 0 < G.d j (f.func x) (f.func y)) :
    feasible G f U i j = ∅ ∧ best G f U i j = ⊤ := by
  have e : feasible G f U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have h := hc.2 hx hy
    rw [hz, mul_zero] at h
    exact hp.not_ge h
  exact ⟨e, best_empty e⟩

theorem feasible_up (ha : a ∈ feasible G f U i j) (h : a ≤ c) :
    c ∈ feasible G f U i j :=
  ⟨ha.1, fun {_ _} hx hy => (ha.2 hx hy).trans (mul_le_mul_left h _)⟩

theorem above_best (h : best G f U i j < c) : c ∈ feasible G f U i j := by
  obtain ⟨a, ha, hac⟩ := sInf_lt_iff.mp h
  exact feasible_up ha hac.le

theorem best_attained (hp : 0 < best G f U i j) (hf : best G f U i j < ⊤) :
    best G f U i j ∈ feasible G f U i j := by
  have ht := above_best hf
  refine ⟨ht.1, fun {x y} hx hy => ?_⟩
  by_cases hz : G.d i x y = 0
  · simpa [hz] using ht.2 hx hy
  by_cases htop : G.d i x y = ⊤
  · simp [htop, ENNReal.mul_top hp.ne']
  apply (ENNReal.div_le_iff hz htop).mp
  exact le_sInf fun c hc => (ENNReal.div_le_iff hz htop).mpr (hc.2 hx hy)

theorem zero_best (h : best G f U i j = 0) (hc : 0 < c) (_hf : c < ⊤) :
    c ∈ feasible G f U i j := above_best (h ▸ hc)

theorem finite_iff : best G f U i j < ⊤ ↔ ∃ c ∈ feasible G f U i j, c < ⊤ :=
  sInf_lt_iff

def discreteGauge : Gauge (Fin 3) Unit 0 where
  d _ x y := if x = y then 0 else ⊤
  metric _ := {
    nonabsorbing := ⟨1, by decide⟩
    dist_self := by simp
    symm := by intro x y; simp [eq_comm]
    triangle := by
      intro x y z
      by_cases h : x = y
      · subst y; simp
      · simp [h]
    isolate_bot := by intro x h; simp [h] }

theorem zero_unattained :
    let f := ident (0 : Fin 3)
    let U := dom f
    U.Nonempty ∧ U ⊆ dom f ∧ best discreteGauge f U () () = 0 ∧
      0 ∉ feasible discreteGauge f U () () := by
  dsimp only
  let f := ident (0 : Fin 3)
  have hp {c : ℝ≥0∞} (hc : 0 < c) : c ∈ feasible discreteGauge f (dom f) () () := by
    refine ⟨Set.Subset.rfl, fun {x y} _ _ => ?_⟩
    by_cases he : x = y <;> simp [discreteGauge, f, ident, he, ENNReal.mul_top hc.ne']
  have h1 : (1 : Fin 3) ∈ dom f := by change (1 : Fin 3) ≠ 0; decide
  have h2 : (2 : Fin 3) ∈ dom f := by change (2 : Fin 3) ≠ 0; decide
  refine ⟨⟨1, h1⟩, Set.Subset.rfl, le_antisymm ?_ (zero_le _), ?_⟩
  · by_contra! h
    obtain ⟨c, hc, hlt⟩ := exists_between h
    exact hlt.not_ge (sInf_le (hp hc))
  · intro hz
    have h := hz.2 h1 h2
    have he : (1 : Fin 3) ≠ 2 := by decide
    simp [discreteGauge, ident, he] at h

def Row (L : Coeff I) (i j : I) := ∀ k, k ≠ i → L k j = 0
def Col (L : Coeff I) (i j : I) := ∀ k, k ≠ j → L i k = 0
def Diagonal (L : Coeff I) := ∀ i j, i ≠ j → L i j = 0

def RowDecoupled (G : Gauge X I b) (f : Operator X b) (U : Set X) (j : I) :=
  ∃ L ∈ lip G f U, ∃ i, Row L i j
def ColDecoupled (G : Gauge X I b) (f : Operator X b) (U : Set X) (i : I) :=
  ∃ L ∈ lip G f U, ∃ j, Col L i j

variable {L K : Coeff I}

omit [Nonempty I] in
theorem erase_input (v : I → ℝ≥0∞) (h : L i j = 0) :
    L i j * v i = 0 ∧ act L v j = ∑ k ∈ Finset.univ.erase i, L k j * v k := by
  refine ⟨by simp [h], ?_⟩
  simpa [act, h] using
    (Finset.univ.add_sum_erase (fun k => L k j * v k) (Finset.mem_univ i)).symm

theorem erase_upper (hL : L ∈ lip G f U) (h : L i j = 0) (hx : x ∈ U) (hy : y ∈ U) :
    G.d j (f.func x) (f.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * G.d k x y :=
  (hL.2 hx hy j).trans_eq (erase_input (vec G x y) h).2

theorem row_bound (hL : L ∈ lip G f U) (hr : Row L i j) (hx : x ∈ U) (hy : y ∈ U) :
    G.d j (f.func x) (f.func y) ≤ L i j * G.d i x y := by
  apply (hL.2 hx hy j).trans_eq
  exact Finset.sum_eq_single i (fun k _ hk => by rw [hr k hk, zero_mul]) (by simp)

theorem column_contribution (_hL : L ∈ lip G f U) (hc : Col L i j)
    (_hx : x ∈ U) (_hy : y ∈ U) (k : I) (hk : k ≠ j) :
    L i k * G.d i x y = 0 := by rw [hc k hk, zero_mul]

theorem diagonal_upper (hL : L ∈ lip G f U) (hd : Diagonal L) (j : I)
    (hx : x ∈ U) (hy : y ∈ U) : G.d j (f.func x) (f.func y) ≤ L j j * G.d j x y :=
  row_bound hL (fun k hk => hd k j hk) hx hy

theorem two_sided (hL : L ∈ lip G f U) (hK : K ∈ coLip G f U) (hr : Row L j j)
    (hx : x ∈ U) (hy : y ∈ U) :
    K j j * G.d j x y ≤ G.d j (f.func x) (f.func y) ∧
    G.d j (f.func x) (f.func y) ≤ L j j * G.d j x y :=
  ⟨co_term hK hx hy j j, row_bound hL hr hx hy⟩

theorem diagonal_bounds (hL : L ∈ lip G f U) (hK : K ∈ coLip G f U) (hd : Diagonal L) :
    ∀ j ⦃x y⦄, x ∈ U → y ∈ U →
      K j j * G.d j x y ≤ G.d j (f.func x) (f.func y) ∧
      G.d j (f.func x) (f.func y) ≤ L j j * G.d j x y :=
  fun j {_ _} hx hy => two_sided hL hK (fun k hk => hd k j hk) hx hy

theorem finite_diagonal (hL : L ∈ lip G f U) (hK : K ∈ coLip G f U) (hd : Diagonal L)
    (hfL : ∀ j, L j j < ⊤) (hfK : ∀ j, K j j < ⊤) :
    ∃ l k : I → ℝ≥0, (∀ j, ↑(l j) = L j j ∧ ↑(k j) = K j j) ∧
      ∀ j ⦃x y⦄, x ∈ U → y ∈ U →
        ↑(k j) * G.d j x y ≤ G.d j (f.func x) (f.func y) ∧
        G.d j (f.func x) (f.func y) ≤ ↑(l j) * G.d j x y := by
  refine ⟨fun j => (L j j).toNNReal, fun j => (K j j).toNNReal, ?_, ?_⟩
  · exact fun j => ⟨ENNReal.coe_toNNReal (hfL j).ne, ENNReal.coe_toNNReal (hfK j).ne⟩
  · intro j x y hx hy
    simpa [ENNReal.coe_toNNReal, (hfL j).ne, (hfK j).ne] using diagonal_bounds hL hK hd j hx hy

theorem positive_channel (hK : K ∈ coLip G f U) (hk : 0 < K i j)
    (hx : x ∈ U) (hy : y ∈ U) (h : 0 < G.d i x y) : 0 < G.d j (f.func x) (f.func y) :=
  (ENNReal.mul_pos hk.ne' h.ne').trans_le (co_term hK hx hy i j)

theorem reflect_zero (hK : K ∈ coLip G f U) (hk : ∀ j, 0 < K j j) (hx : x ∈ U) (hy : y ∈ U)
    (h : GaugeZeroRelated G.d (f.func x) (f.func y)) : GaugeZeroRelated G.d x y := by
  intro j
  by_contra hn
  exact (positive_channel hK (hk j) hx hy (pos_iff_ne_zero.mpr hn)).ne' (h j)

end
end HCH02
```

```text filename=lean-toolchain
leanprover/lean4:v4.29.1
```

```toml filename=lakefile.toml
name = "HCH02"
version = "0.1.0"
defaultTargets = ["ChapterTwo"]

[[require]]
name = "mathlib"
git = "https://github.com/leanprover-community/mathlib4.git"
rev = "5e932f97dd25535344f80f9dd8da3aab83df0fe6"

[[lean_lib]]
name = "ChapterTwo"
roots = [
  "Main", "Bounds", "Chains", "Channels",
  "formal_oet.vol_01.ch_01_foundations.gauge_space",
  "formal_oet.vol_01.ch_01_foundations.operator_space"
]
```

```json filename=lake-manifest.json
{
  "version": "1.1.0",
  "name": "HCH02",
  "lakeDir": ".lake",
  "packagesDir": ".lake/packages",
  "packages": [
    {"name":"mathlib","scope":"","type":"git","url":"https://github.com/leanprover-community/mathlib4.git","rev":"5e932f97dd25535344f80f9dd8da3aab83df0fe6","inputRev":"5e932f97dd25535344f80f9dd8da3aab83df0fe6","configFile":"lakefile.lean","inherited":false},
    {"name":"plausible","scope":"leanprover-community","type":"git","url":"https://github.com/leanprover-community/plausible","rev":"83e90935a17ca19ebe4b7893c7f7066e266f50d3","inputRev":"main","configFile":"lakefile.toml","inherited":true},
    {"name":"LeanSearchClient","scope":"leanprover-community","type":"git","url":"https://github.com/leanprover-community/LeanSearchClient","rev":"c5d5b8fe6e5158def25cd28eb94e4141ad97c843","inputRev":"main","configFile":"lakefile.toml","inherited":true},
    {"name":"importGraph","scope":"leanprover-community","type":"git","url":"https://github.com/leanprover-community/import-graph","rev":"48d5698bc464786347c1b0d859b18f938420f060","inputRev":"main","configFile":"lakefile.toml","inherited":true},
    {"name":"proofwidgets","scope":"leanprover-community","type":"git","url":"https://github.com/leanprover-community/ProofWidgets4","rev":"4dd0959c44d1af0462bd604d0f87c5781307d709","inputRev":"v0.0.95+lean-v4.29.1","configFile":"lakefile.lean","inherited":true},
    {"name":"aesop","scope":"leanprover-community","type":"git","url":"https://github.com/leanprover-community/aesop","rev":"7152850e7b216a0d409701617721b6e469d34bf6","inputRev":"master","configFile":"lakefile.toml","inherited":true},
    {"name":"Qq","scope":"leanprover-community","type":"git","url":"https://github.com/leanprover-community/quote4","rev":"707efb56d0696634e9e965523a1bbe9ac6ce141d","inputRev":"master","configFile":"lakefile.toml","inherited":true},
    {"name":"batteries","scope":"leanprover-community","type":"git","url":"https://github.com/leanprover-community/batteries","rev":"756e3321fd3b02a85ffda19fef789916223e578c","inputRev":"main","configFile":"lakefile.toml","inherited":true},
    {"name":"Cli","scope":"leanprover","type":"git","url":"https://github.com/leanprover/lean4-cli","rev":"7802da01beb530bf051ab657443f9cd9bc3e1a29","inputRev":"v4.29.0","configFile":"lakefile.toml","inherited":true}
  ]
}
```

```json filename=alignment.json
{
  "case_id":"HCH02",
  "version":"0.1.0",
  "items":[
    {"id":"HC02-D01","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.Gauge"},{"file":"Bounds.lean","name":"HCH02.vec"},{"file":"Bounds.lean","name":"HCH02.lip"},{"file":"Bounds.lean","name":"HCH02.globalLip"},{"file":"Bounds.lean","name":"HCH02.lip_iff"},{"file":"Bounds.lean","name":"HCH02.top_entry"}],
     "representation":"有限非空 I 上的 Gauge 为每个分量携带冻结的扩展伪度量公理。lip_iff 展开 U⊆dom f 和每个点对、每个输出的 ENNReal 和式。globalLip 取 U=dom f。top_entry 给出无穷系数遇到零或正输入距的结果。",
     "dependencies":["HC02-D03"]},
    {"id":"HC02-D02","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.coLip"},{"file":"Bounds.lean","name":"HCH02.coLip_iff"},{"file":"Bounds.lean","name":"HCH02.co_term"}],
     "representation":"合法集同时要求 U 非空、U⊆dom f 及每个点对、每个输出的整行下界。co_term 从整行和导出任意指定输入项的下界。",
     "dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-D03","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.Coeff"},{"file":"Bounds.lean","name":"HCH02.display"},{"file":"Bounds.lean","name":"HCH02.display_entry"},{"file":"Bounds.lean","name":"HCH02.mul"},{"file":"Bounds.lean","name":"HCH02.display_mul"},{"file":"Bounds.lean","name":"HCH02.act"},{"file":"Bounds.lean","name":"HCH02.act_mul"},{"file":"Bounds.lean","name":"HCH02.act_mono"},{"file":"Bounds.lean","name":"HCH02.term_le_act"}],
     "representation":"A i j 表示输入 i 到输出 j。display_entry 给出通常矩阵的第 j 行第 i 列。mul B A i j 对 k 求 B k j 乘 A i k 的和，display_mul 证明它对应通常乘法。",
     "dependencies":[]},
    {"id":"HC02-D04","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.unitM"},{"file":"Bounds.lean","name":"HCH02.display_unit"},{"file":"Bounds.lean","name":"HCH02.act_unit"},{"file":"Bounds.lean","name":"HCH02.mul_unit"},{"file":"Chains.lean","name":"HCH02.product"},{"file":"Chains.lean","name":"HCH02.product_empty"},{"file":"Chains.lean","name":"HCH02.product_step"},{"file":"Chains.lean","name":"HCH02.product_one"},{"file":"Chains.lean","name":"HCH02.display_product"}],
     "representation":"Fin n 按施行先后编号。单位条目是 Kronecker δ，添末步对应左乘。通常矩阵显示的乘积等于逆序列表乘积。空积和单步积分别化为单位和唯一矩阵。",
     "dependencies":["HC02-D03"]},
    {"id":"HC02-D05","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.ident"},{"file":"Bounds.lean","name":"HCH02.comp"},{"file":"Bounds.lean","name":"HCH02.comp_domain"},{"file":"Chains.lean","name":"HCH02.run"},{"file":"Chains.lean","name":"HCH02.run_eq_chain"},{"file":"Chains.lean","name":"HCH02.stage"},{"file":"Chains.lean","name":"HCH02.stage_zero"},{"file":"Chains.lean","name":"HCH02.stage_succ"},{"file":"Chains.lean","name":"HCH02.stage_last"},{"file":"Chains.lean","name":"HCH02.stages_unique"},{"file":"Chains.lean","name":"HCH02.final_image"},{"file":"Chains.lean","name":"HCH02.stage_domain"},{"file":"Chains.lean","name":"HCH02.OnStages"},{"file":"Chains.lean","name":"HCH02.onStages_iff"}],
     "representation":"stage 用前缀复合的像表示输入域。证明了起始域、逐步取像、终像以及各步域包含。任意给定的递推域列均与 stage 相等，onStages_iff 将该域列上的逐步数据转换成链前提。run_eq_chain 对应冻结的复合顺序。",
     "dependencies":["HC02-D03"]},
    {"id":"HC02-D06","status":"complete",
     "declarations":[{"file":"Chains.lean","name":"HCH02.Path"},{"file":"Chains.lean","name":"HCH02.edge"},{"file":"Chains.lean","name":"HCH02.weight"},{"file":"Chains.lean","name":"HCH02.HasZero"},{"file":"Chains.lean","name":"HCH02.AllPositive"},{"file":"Chains.lean","name":"HCH02.one_path"},{"file":"Chains.lean","name":"HCH02.sum_paths"}],
     "representation":"n+1 步的自由中间序列是整个 Fin n → I。Fin.cons i p 与 Fin.snoc p j 给出各边的起止指标。weight 乘遍所有边，两个谓词分别量化某条零边和每条正边。单步路径唯一，并证明矩阵条目等于所有路径权重之和。",
     "dependencies":["HC02-D03","HC02-D04"]},
    {"id":"HC02-D07","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.Channel"},{"file":"Channels.lean","name":"HCH02.Row"},{"file":"Channels.lean","name":"HCH02.Col"},{"file":"Channels.lean","name":"HCH02.Diagonal"},{"file":"Channels.lean","name":"HCH02.RowDecoupled"},{"file":"Channels.lean","name":"HCH02.ColDecoupled"}],
     "representation":"通道取 I×I。Row 固定输出 j，允许任意输入 i 为支撑。Col 固定输入 i，允许任意输出 j 为支撑。行、列解耦均存在量化合法矩阵及支撑位置。Diagonal 要求全部非对角条目为零。",
     "dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-D08","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.feasible"},{"file":"Channels.lean","name":"HCH02.feasible_iff"},{"file":"Channels.lean","name":"HCH02.best"},{"file":"Channels.lean","name":"HCH02.best_empty"}],
     "representation":"在合法域上，feasible_iff 将成员资格等同于对所有点对的单输入标量不等式。best 取该 ENNReal 集合的 sInf，空集给出 ⊤。",
     "dependencies":["HC02-D01"]},
    {"id":"HC02-P01","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.singleton_lip"}],
     "representation":"对非空次单类型 I 及其元素 i，全域矩阵合法性等价于所有定义域点对满足唯一的标量上界。",
     "dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-P02","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.global_restrict"}],
     "representation":"将全域证书族限制到任意 U⊆dom f，得到集合包含。",
     "dependencies":["HC02-D01","HC02-P03"]},
    {"id":"HC02-P03","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.lip_shrink"}],
     "representation":"从 U⊆V 和 V 上的合法性导出 U 上的合法性，V⊆dom f 由原证书给出。",
     "dependencies":["HC02-D01"]},
    {"id":"HC02-P04","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.entryInf"},{"file":"Bounds.lean","name":"HCH02.entryInf_mono"}],
     "representation":"对证书族经 A↦A i j 的像取 sInf。域从 V 缩到 U 时，这个条目下确界只能减小或相等。",
     "dependencies":["HC02-D01","HC02-P03"]},
    {"id":"HC02-P05","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.lip_comp"}],
     "representation":"起点域包含于两步复合定义域，第二个证书取在 f.func '' U。对像点应用第二步，再用矩阵作用的单调性合并为 mul B A。",
     "dependencies":["HC02-D01","HC02-D03","HC02-D05"]},
    {"id":"HC02-P06","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.collapsed_entry"}],
     "representation":"在 dom f 内将输出零距、输入正距的点对代入单项下界，得到每个全域 co-Lip 矩阵的该条目为零。",
     "dependencies":["HC02-D02"]},
    {"id":"HC02-P07","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.co_comp"}],
     "representation":"第二步在实际像域上给出整行下界。连乘得到原域上的合法下界，非空性由第一步证书给出。",
     "dependencies":["HC02-D02","HC02-D03","HC02-D05"]},
    {"id":"HC02-P08","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.CloseOn"},{"file":"Bounds.lean","name":"HCH02.close_swap"},{"file":"Bounds.lean","name":"HCH02.perturb"}],
     "representation":"在公共定义域子集 U 上，对任意 x,y∈U 和 j，三角不等式与两个逐点扰动界给出第二算子的像距至多为第一算子的像距加两次 δ j。",
     "dependencies":["HC02-D01"]},
    {"id":"HC02-P09","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.perturb_rev"}],
     "representation":"在同一逐点前提下，用分量对称性交换两个算子，得到第一算子像距的反向估计。",
     "dependencies":["HC02-P08"]},
    {"id":"HC02-P10","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.lip_bridge"},{"file":"Bounds.lean","name":"HCH02.lip_bridge_rev"}],
     "representation":"把所选上界证书的行和代入扰动界，误差为 2*δ j。两个声明分别以第一、第二算子的证书为前提。",
     "dependencies":["HC02-D01","HC02-P08"]},
    {"id":"HC02-P11","status":"complete",
     "declarations":[{"file":"Bounds.lean","name":"HCH02.co_bridge"},{"file":"Bounds.lean","name":"HCH02.co_bridge_rev"}],
     "representation":"把所选下界证书的行和放在另一算子像距加 2*δ j 的下方，给出两个证书方向。",
     "dependencies":["HC02-D02","HC02-P08","HC02-P09"]},
    {"id":"HC02-P12","status":"complete",
     "declarations":[{"file":"Chains.lean","name":"HCH02.chain_lip"}],
     "representation":"对任意 Fin n 步，逐步前提只涉及实际输入域。按末步归纳得到指定有序乘积是整个复合的局部上界，包含所有正长度。",
     "dependencies":["HC02-D04","HC02-D05","HC02-P05","HC02-P14"]},
    {"id":"HC02-P13","status":"complete",
     "declarations":[{"file":"Chains.lean","name":"HCH02.chain_coLip"}],
     "representation":"对 n+1 步，从首个实际域的 co-Lip 成员资格推出起始域非空。对前缀和末步归纳得到指定乘积的 co-Lip 成员资格。",
     "dependencies":["HC02-D02","HC02-D04","HC02-D05","HC02-P07","HC02-P15"]},
    {"id":"HC02-P14","status":"complete",
     "declarations":[{"file":"Chains.lean","name":"HCH02.id_lip"}],
     "representation":"空链和空积分别化为 ident 与 unitM。恒等算子的单位上界对全部合法 U 成立，因而也适用于原文的非空 U。",
     "dependencies":["HC02-D01","HC02-D04","HC02-D05"]},
    {"id":"HC02-P15","status":"complete",
     "declarations":[{"file":"Chains.lean","name":"HCH02.id_coLip"}],
     "representation":"对非空 U⊆dom ident，单位矩阵作用保持距离向量，给出零步合法下界。",
     "dependencies":["HC02-D02","HC02-D04","HC02-D05"]},
    {"id":"HC02-P16","status":"complete",
     "declarations":[{"file":"Chains.lean","name":"HCH02.path_criteria"},{"file":"Chains.lean","name":"HCH02.one_path"}],
     "representation":"path_criteria 第一合取项保留正长度算子链、起始域及两族实际证书。指定 Lip 乘积条目为零，当且仅当每个中间序列含零边。单步时化为唯一条目为零。",
     "dependencies":["HC02-D06"]},
    {"id":"HC02-P17","status":"complete",
     "declarations":[{"file":"Chains.lean","name":"HCH02.path_criteria"},{"file":"Chains.lean","name":"HCH02.one_path"}],
     "representation":"同一链前提下的第二合取项表明，指定 co-Lip 乘积条目为正，当且仅当有一条每条边均为正的路径。单步时化为唯一条目为正。",
     "dependencies":["HC02-D06"]},
    {"id":"HC02-P18","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.empty_channel"}],
     "representation":"U 中存在零输入距、正输出距的一对点时，一切扩展标量均违反该点对上界，故可行集为空且 best=⊤。",
     "dependencies":["HC02-D08"]},
    {"id":"HC02-P19","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.best_attained"}],
     "representation":"0<best<⊤ 时证明 best 属于可行集。对输入距为零、为无穷、为有限正数分别处理，有限正情形用除法和下确界的泛性质。",
     "dependencies":["HC02-D08","HC02-P21"]},
    {"id":"HC02-P20","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.feasible_up"}],
     "representation":"从 a 的可行性及 a≤c 推出 c 对全部点对可行。",
     "dependencies":["HC02-D08"]},
    {"id":"HC02-P21","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.above_best"}],
     "representation":"每个严格大于 best 的扩展标量 c 都可行，涵盖正有限下确界及 c=⊤。由下确界先取一个小于 c 的可行常数，再向上放宽。",
     "dependencies":["HC02-D08","HC02-P20"]},
    {"id":"HC02-P22","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.zero_best"}],
     "representation":"best=0 时，每个严格正且有限的 c 都在可行集中。",
     "dependencies":["HC02-P21"]},
    {"id":"HC02-P23","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.discreteGauge"},{"file":"Channels.lean","name":"HCH02.zero_unattained"}],
     "representation":"取 X=Fin 3、I=Unit、吸收元 0，异点距离为 ⊤，取恒等算子及其非空定义域。所有正标量可行，由稠密性得下确界为零。点 1、2 排除零标量。",
     "dependencies":["HC02-D01","HC02-D05","HC02-D08"]},
    {"id":"HC02-P24","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.finite_iff"}],
     "representation":"best<⊤ 等价于存在一个小于 ⊤ 且对全部点对可行的标量。等价性直接来自下确界的严格上界判据。",
     "dependencies":["HC02-D08"]},
    {"id":"HC02-P25","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.erase_input"},{"file":"Channels.lean","name":"HCH02.erase_upper"}],
     "representation":"系数为零时乘积项为零，整行和等于删除 i 后的和。对合法 L 得到删项后的输出上界，输入距允许为 ⊤。",
     "dependencies":["HC02-D01","HC02-D03"]},
    {"id":"HC02-P26","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.row_bound"}],
     "representation":"对任意 i,j，第 j 行在 i 以外为零时，对所有 U 内点对将输出上界化为 L i j 乘第 i 个输入距。",
     "dependencies":["HC02-D01","HC02-D03","HC02-D07"]},
    {"id":"HC02-P27","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.column_contribution"}],
     "representation":"对选定的合法 L 和任意域内点对，Col L i j 保证每个 k≠j 的输入 i 贡献为零。",
     "dependencies":["HC02-D07"]},
    {"id":"HC02-P28","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.diagonal_upper"}],
     "representation":"对角合法 L 的每行都在对角位置满足 Row，因而所有分量分别有标量上界。",
     "dependencies":["HC02-D07","HC02-P26"]},
    {"id":"HC02-P29","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.two_sided"}],
     "representation":"仅要求 L 的第 j 行在对角位置外为零。K 的对角单项下界与 L 的标量上界合成同一点对的双侧界。",
     "dependencies":["HC02-D02","HC02-P26"]},
    {"id":"HC02-P30","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.diagonal_bounds"},{"file":"Channels.lean","name":"HCH02.finite_diagonal"}],
     "representation":"对所有 j 同时应用双侧界。两族对角条目均有限时，构造 NNReal 系数族，证明其嵌入逐项等于原条目并满足同一双侧界。",
     "dependencies":["HC02-D07","HC02-P29"]},
    {"id":"HC02-P31","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.positive_channel"}],
     "representation":"在合法 co-Lip 证书的正通道上，正输入距乘以正系数仍为正。单项下界推出相应输出距为正。",
     "dependencies":["HC02-D02"]},
    {"id":"HC02-P32","status":"complete",
     "declarations":[{"file":"Channels.lean","name":"HCH02.reflect_zero"}],
     "representation":"全部对角通道为正时，逐分量反用正距保持，证明像点的冻结 GaugeZeroRelated 关系蕴含原点对的同一关系。",
     "dependencies":["HC02-P31"]}
  ]
}
```

**完成情况**　已按冻结原文与 `obligations.json` 严格对齐整章。8 项定义及表示、32 项命题及反例全部完成。未完成项 0，未确认项 0。