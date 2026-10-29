import RecordLayers

namespace MathGauge.F110

variable {X Y : Type*} [DecidableEq Y]

/-- 动力系统轨道：从 x 出发迭代 n 步的状态 f^[n](x) -/
def orbit (f : X → X) : ℕ → X → X
  | 0, x => x
  | n + 1, x => orbit f n (f x)

/-- 安全集合谓词：所有演化时刻的观测值始终属于有限集合 B -/
def Safe (B : Finset Y) (q : X → Y) (f : X → X) (x : X) : Prop :=
  ∀ n, q (orbit f n x) ∈ B

/-- 原题面的演化条件：对每个 x ∈ A（即 q x ∈ B），q (f x) = q x 或 q (f x) = g (q x) -/
def Evolves (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → q (f x) = q x ∨ q (f x) = g (q x)

/-- 附加条件（严格确定性实现）：对每个 x ∈ A，演化严格满足 q (f x) = g (q x) -/
def Realizes (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y) : Prop :=
  ∀ x, q x ∈ B → q (f x) = g (q x)

/-- 附加条件严格强于原题面演化条件 -/
theorem realizes_implies_evolves (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) : Evolves B q f g :=
  fun x hx => Or.inr (h x hx)

/-- 安全状态单步前向演化仍保持安全 -/
theorem safe_step (B : Finset Y) (q : X → Y) (f : X → X) {x : X}
    (hx : Safe B q f x) : Safe B q f (f x) := by
  intro n
  exact hx (n + 1)

/-- 不变子集上的轨道包含引理 -/
theorem orbit_mem_of_invariant (f : X → X) (S : Set X) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ (n : ℕ) {x : X}, x ∈ S → orbit f n x ∈ S
  | 0, _, hx => hx
  | n + 1, x, hx => by
    change orbit f n (f x) ∈ S
    exact orbit_mem_of_invariant f S hS n (hS x hx)

/-- 真正的安全集合 K 在 A 中的最大性（一般动力系统下均成立） -/
theorem safe_maximal (B : Finset Y) (q : X → Y) (f : X → X) (S : Set X)
    (hB : ∀ x ∈ S, q x ∈ B) (hS : ∀ x ∈ S, f x ∈ S) :
    ∀ x ∈ S, Safe B q f x := by
  intro x hx n
  exact hB _ (orbit_mem_of_invariant f S hS n hx)

/-- 附加条件 Realizes 下安全点在各记录层中的包含性 -/
theorem safe_in_layers (B : Finset Y) (q : X → Y) (f : X → X) (g : Y → Y)
    (h : Realizes B q f g) : ∀ (n : ℕ) {x : X}, Safe B q f x → q x ∈ layers B g n
  | 0, _, hx => hx 0
  | n + 1, x, hx => by
    rw [layers, Finset.mem_filter]
    refine ⟨hx 0, ?_⟩
    rw [← h x (hx 0)]
    exact safe_in_layers B q f g h n (safe_step B q f hx)

end MathGauge.F110
