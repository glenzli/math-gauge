import OrbitModel

namespace MathGauge.F110

variable {X Y : Type*} [DecidableEq Y]

/-!
### 1. 原主张的审查与形式化反例

原题面演化条件允许停滞（`q (f x) = q x`）。当 `g (q x) ∉ B` 时系统若选择停滞，
则该状态依然安全（属于 `K`），但被 `terminal B g` 排除。因此原主张在原条件下不成立。
-/

def cex_X : Type := Unit
def cex_Y : Type := Bool
def cex_B : Finset Bool := {false}
def cex_q : Unit → Bool := fun _ => false
def cex_f : Unit → Unit := id
def cex_g : Bool → Bool := fun _ => true

theorem cex_evolves : Evolves cex_B cex_q cex_f cex_g := by
  intro x _
  left
  rfl

theorem cex_safe : Safe cex_B cex_q cex_f () := by
  intro n
  have horbit : orbit cex_f n () = () := by
    induction n with
    | zero => rfl
    | succ n ih =>
      change orbit cex_f n (cex_f ()) = ()
      exact ih
  change cex_q (orbit cex_f n ()) ∈ cex_B
  rw [horbit]
  exact Finset.mem_singleton.mpr rfl

theorem cex_not_terminal : cex_q () ∉ terminal cex_B cex_g := by
  intro h
  have hmem := (terminal_mem cex_B cex_g (cex_q ())).mp h
  have hstep := (terminal_mem cex_B cex_g (cex_g (cex_q ()))).mp hmem.2
  have htrue : (true : Bool) ∈ ({false} : Finset Bool) := hstep.1
  rw [Finset.mem_singleton] at htrue
  cases htrue

/-- 形式化反例：存在系统满足原演化条件 Evolves，但真正安全集不被 terminal 覆盖 -/
theorem counterexample :
    ∃ (X Y : Type) (_ : DecidableEq Y) (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y),
      Evolves B q f g ∧ ∃ x : X, Safe B q f x ∧ q x ∉ terminal B g :=
  ⟨cex_X, cex_Y, inferInstance, cex_B, cex_q, cex_f, cex_g, cex_evolves, (), cex_safe, cex_not_terminal⟩

/-- 原主张在原演化条件 Evolves 下不成立 -/
theorem original_claim_false :
    ¬ (∀ (X Y : Type) [DecidableEq Y] (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y),
        Evolves B q f g → ∀ x, Safe B q f x ↔ q x ∈ terminal B g) := by
  intro h
  exact cex_not_terminal ((h cex_X cex_Y cex_B cex_q cex_f cex_g cex_evolves ()).mp cex_safe)

/-!
### 2. 原条件下保留的可证明单向包含

在原演化条件 Evolves 下，`q⁻¹(terminal B g) ⊆ K` 依然成立。
-/

theorem terminal_implies_safe_of_evolves (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Evolves B q f g) : ∀ (n : ℕ) {x : X}, q x ∈ terminal B g → q (orbit f n x) ∈ B
  | 0, x, hx => ((terminal_mem B g (q x)).mp hx).1
  | n + 1, x, hx => by
    have hx' := (terminal_mem B g (q x)).mp hx
    have hf : q (f x) ∈ terminal B g := by
      rcases h x hx'.1 with hq | hg
      · rw [hq]; exact hx
      · rw [hg]; exact hx'.2
    change q (orbit f n (f x)) ∈ B
    exact terminal_implies_safe_of_evolves B q f g h n hf

/-- 原条件下的包含定理：`q x ∈ terminal B g → Safe B q f x` -/
theorem terminal_subset_safe (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Evolves B q f g) {x : X} (hx : q x ∈ terminal B g) : Safe B q f x :=
  fun n => terminal_implies_safe_of_evolves B q f g h n hx

/-!
### 3. 恢复等式的附加条件及其证明

附加条件：严格确定性实现条件 `Realizes B q f g`（消除了停滞分支）。
在此附加条件下，`Safe ↔ terminal` 等式得以恢复。
-/

/-- 附加条件下的等式恢复定理 -/
theorem exact_realization_of_realizes (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (x : X) :
    Safe B q f x ↔ q x ∈ terminal B g :=
  ⟨safe_in_layers B q f g h B.card,
   terminal_subset_safe B q f g (realizes_implies_evolves B q f g h)⟩

/-- 兼容原命名（注：依赖附加条件 Realizes，不可作为原主张） -/
theorem exact_realization (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (x : X) :
    Safe B q f x ↔ q x ∈ terminal B g :=
  exact_realization_of_realizes B q f g h x

/-!
### 4. 原条件下真正安全集合 K 的前向不变性与最大性
-/

/-- 原条件下真正安全集 K 的前向不变性 -/
theorem safe_invariant (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) : Safe B q f (f x) :=
  safe_step B q f hx

/-- 原条件下真正安全集 K 是 A 中最大的 f-前向不变集 -/
theorem safe_maximal_of_evolves (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (_h : Evolves B q f g) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, Safe B q f x :=
  safe_maximal B q f S hB hS

/-- 附加条件 Realizes 下终端层诱导集为最大不变集（原附件证明的真实内涵） -/
theorem maximal_invariant_of_realizes (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, q x ∈ terminal B g := by
  intro x hx
  exact (exact_realization_of_realizes B q f g h x).mp (safe_maximal B q f S hB hS x hx)

/-- 兼容原命名 -/
theorem maximal_invariant (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, q x ∈ terminal B g :=
  maximal_invariant_of_realizes B q f g h S hB hS

#print axioms counterexample
#print axioms original_claim_false
#print axioms terminal_subset_safe
#print axioms exact_realization_of_realizes
#print axioms safe_maximal_of_evolves

end MathGauge.F110
