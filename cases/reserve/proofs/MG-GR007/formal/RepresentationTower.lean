import LinearTower
import Mathlib.RepresentationTheory.Intertwining

noncomputable section
open Function Representation
namespace MathGauge.RepresentationTower
universe u v w z
variable {k : Type u} [Field k] {G : Type v} [Monoid G]
variable {B : ℕ → Type w} [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
variable {C : Type z} [AddCommGroup C] [Module k C]
variable (ρ : ∀ n, Representation k G (B n)) (σ : Representation k G C)
variable (b : ∀ n, (ρ (n+1)).IntertwiningMap (ρ n))
variable (q : ∀ n, (ρ n).IntertwiningMap σ)

/-- The actual vector space of coherent coordinate families. -/
def limit : Submodule k (∀ n, B n) where
  carrier := {x | ∀ n, b n (x (n+1)) = x n}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy n; simp only [Pi.add_apply, map_add, hx n, hy n]
  smul_mem' := by intro a x hx n; simp only [Pi.smul_apply, map_smul, hx n]

/-- Coordinatewise action on the coherent families. -/
def limitRep : Representation k G (limit ρ b) where
  toFun g :=
    { toFun := fun x => ⟨fun n => ρ n g (x.val n), by
        intro n
        rw [(b n).isIntertwining, x.property n]⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp

@[simp] theorem limitRep_apply (g : G) (x : limit ρ b) (n : ℕ) :
    ((limitRep ρ b g) x).val n = ρ n g (x.val n) := rfl

/-- The finite-dimensional stabilization theorem applies to the actual spaces of equivariant maps. -/
theorem coherent_sections [FiniteDimensional k C] [∀ n, FiniteDimensional k (B n)]
    (hq : ∀ n, (q n).comp (b n) = q (n+1))
    (hs : ∀ n, ∃ s : σ.IntertwiningMap (ρ n), (q n).comp s = IntertwiningMap.id σ) :
    ∃ s : ∀ n, σ.IntertwiningMap (ρ n),
      (∀ n, (q n).comp (s n) = IntertwiningMap.id σ) ∧
      (∀ n, (b n).comp (s (n+1)) = s n) := by
  let bet := fun n => IntertwiningMap.llcomp σ (ρ (n+1)) (ρ n) (b n)
  let quo := fun n => IntertwiningMap.llcomp σ (ρ n) σ (q n)
  have hquo : ∀ n, (quo n).comp (bet n) = quo (n+1) := by
    intro n
    ext s c
    exact congrArg (fun f : (ρ (n+1)).IntertwiningMap σ => f (s c)) (hq n)
  exact MathGauge.LinearTower.coherent_fiber bet quo hquo (IntertwiningMap.id σ) hs

/-- A coherent section family yields the stated equivariant section into the limit. -/
def assemble (s : ∀ n, σ.IntertwiningMap (ρ n))
    (hs : ∀ n, (b n).comp (s (n+1)) = s n) :
    σ.IntertwiningMap (limitRep ρ b) where
  toLinearMap :=
    { toFun := fun c => ⟨fun n => s n c, fun n => congrArg (fun f => f c) (hs n)⟩
      map_add' := by intro x y; ext n; exact (s n).map_add x y
      map_smul' := by intro a x; ext n; exact (s n).map_smul a x }
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    funext n
    change s n (σ g c) = ρ n g (s n c)
    exact IntertwiningMap.isIntertwining σ (ρ n) (s n) g c

/-- Evaluation of the common record is the first row's actual quotient map. -/
def record : (limitRep ρ b).IntertwiningMap σ where
  toLinearMap :=
    { toFun := fun x => q 0 (x.val 0)
      map_add' := by intro x y; exact (q 0).map_add _ _
      map_smul' := by intro a x; exact (q 0).map_smul _ _ }
  isIntertwining' := by
    intro g
    apply LinearMap.ext
    intro x
    change q 0 (ρ 0 g (x.val 0)) = σ g (q 0 (x.val 0))
    exact IntertwiningMap.isIntertwining (ρ 0) σ (q 0) g _

theorem record_coordinate (hq : ∀ n, (q n).comp (b n) = q (n+1))
    (x : limit ρ b) (n : ℕ) : q n (x.val n) = record ρ σ b q x := by
  induction n with
  | zero => rfl
  | succ n ih =>
    calc
      q (n+1) (x.val (n+1)) = q n (b n (x.val (n+1))) := by
        exact (congrArg (fun f : (ρ (n+1)).IntertwiningMap σ => f (x.val (n+1))) (hq n)).symm
      _ = q n (x.val n) := congrArg (q n) (x.property n)
      _ = _ := ih

theorem record_assemble (s : ∀ n, σ.IntertwiningMap (ρ n))
    (hs : ∀ n, (b n).comp (s (n+1)) = s n)
    (hq : ∀ n, (q n).comp (s n) = IntertwiningMap.id σ) :
    (record ρ σ b q).comp (assemble ρ σ b s hs) = IntertwiningMap.id σ := by
  exact hq 0

end MathGauge.RepresentationTower
