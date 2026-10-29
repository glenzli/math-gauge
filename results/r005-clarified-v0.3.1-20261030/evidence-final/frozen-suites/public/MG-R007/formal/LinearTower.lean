import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.Tactic

noncomputable section
open Function
namespace MathGauge.LinearTower
universe u v w
variable {k : Type u} [Field k]
variable {V : ℕ → Type v} [∀ n, AddCommGroup (V n)] [∀ n, Module k (V n)]
variable (b : ∀ n, V (n+1) →ₗ[k] V n)

/-- The actual composite of the given adjacent transition maps. -/
def down (n m : ℕ) (h : n ≤ m) : V m →ₗ[k] V n :=
  Nat.leRecOn h (fun {j} p => p.comp (b j)) (LinearMap.id)

@[simp] theorem down_self (n : ℕ) : down b n n le_rfl = LinearMap.id := by
  exact Nat.leRecOn_self _

@[simp] theorem down_succ (n m : ℕ) (h : n ≤ m) :
    down b n (m+1) (Nat.le_succ_of_le h) = (down b n m h).comp (b m) := by
  simp [down, Nat.leRecOn_succ h]

@[simp] theorem down_adjacent (n : ℕ) : down b n (n+1) (Nat.le_succ n) = b n := by
  rw [down_succ b n n le_rfl, down_self]; simp

theorem down_comp (n m l : ℕ) (h : n ≤ m) (h' : m ≤ l) :
    down b n l (h.trans h') = (down b n m h).comp (down b m l h') := by
  induction l, h' using Nat.le_induction with
  | base => simp
  | succ l hl ih =>
    rw [down_succ b n l (h.trans hl), down_succ b m l hl, ih]
    rfl

/-- No unproved stabilization is a field of the tower; it follows from finite dimension. -/
theorem ranges_stabilize [∀ n, FiniteDimensional k (V n)] (n : ℕ) :
    ∃ N, ∃ hN : n ≤ N, ∀ m, ∀ hm : N ≤ m,
      LinearMap.range (down b n N hN) =
      LinearMap.range (down b n m (hN.trans hm)) := by
  let r : ℕ →o (Submodule k (V n))ᵒᵈ :=
    { toFun := fun j => LinearMap.range (down b n (n+j) (Nat.le_add_right n j))
      monotone' := by
        intro i j hij
        change LinearMap.range (down b n (n+j) _) ≤ LinearMap.range (down b n (n+i) _)
        rw [down_comp b n (n+i) (n+j) (by omega) (by omega)]
        exact LinearMap.range_comp_le_range _ _ }
  obtain ⟨j,hj⟩ := IsArtinian.monotone_stabilizes r
  refine ⟨n+j, by omega, ?_⟩
  intro m hm
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (by omega : n ≤ m)
  exact hj d (by omega)

/-- Canonical stable image as the intersection of all actual ranges. -/
def stable (n : ℕ) : Submodule k (V n) :=
  ⨅ (m : ℕ) (h : n ≤ m), LinearMap.range (down b n m h)

theorem mem_stable_iff (n : ℕ) (x : V n) :
    x ∈ stable b n ↔ ∀ (m : ℕ) (h : n ≤ m), ∃ y, down b n m h y = x := by
  simp [stable, LinearMap.mem_range]

theorem stable_eq_range [∀ n, FiniteDimensional k (V n)] (n : ℕ) :
    ∃ N, ∃ h : n ≤ N, ∀ m, ∀ hm : N ≤ m,
      stable b n = LinearMap.range (down b n m (h.trans hm)) := by
  obtain ⟨N,hN,h⟩ := ranges_stabilize b n
  refine ⟨N,hN,fun m hm => le_antisymm (iInf_le_of_le m (iInf_le _ _)) ?_⟩
  intro x hx
  rw [mem_stable_iff]
  intro l hl
  let r := max m l
  have hNr : N ≤ r := hm.trans (le_max_left _ _)
  have hrange : LinearMap.range (down b n m (by omega)) =
      LinearMap.range (down b n r (by omega)) := (h m hm).symm.trans (h r hNr)
  rw [hrange] at hx
  obtain ⟨y,hy⟩ := hx
  refine ⟨down b l r (le_max_right _ _) y, ?_⟩
  rw [← LinearMap.comp_apply, ← down_comp]
  exact hy

variable {W : Type w} [AddCommGroup W] [Module k W]
variable (q : ∀ n, V n →ₗ[k] W)
variable (hq : ∀ n, (q n).comp (b n) = q (n+1))
include hq

theorem down_record (n m : ℕ) (h : n ≤ m) :
    (q n).comp (down b n m h) = q m := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [down_succ b n m hm]
    rw [← LinearMap.comp_assoc, ih, hq]

/-- Finite-dimensional fibers admit a coherent lift without assuming surjective transitions. -/
theorem coherent_fiber [∀ n, FiniteDimensional k (V n)] (c : W)
    (hc : ∀ n, ∃ x, q n x = c) :
    ∃ x : ∀ n, V n, (∀ n, q n (x n) = c) ∧ (∀ n, b n (x (n+1)) = x n) := by
  let S := fun n => {x : V n // x ∈ stable b n ∧ q n x = c}
  have hn : ∀ n, Nonempty (S n) := by
    intro n
    obtain ⟨N,hN,h⟩ := stable_eq_range b n
    obtain ⟨x,hx⟩ := hc N
    refine ⟨⟨down b n N hN x, ?_, ?_⟩⟩
    · rw [h N le_rfl]; exact ⟨x,rfl⟩
    · change ((q n).comp (down b n N hN)) x = c
      rw [down_record b q hq]; exact hx
  have lift : ∀ n, ∀ x : S n, ∃ y : S (n+1), b n y.val = x.val := by
    intro n x
    obtain ⟨N,hN,hN'⟩ := stable_eq_range b (n+1)
    obtain ⟨z,hz⟩ := (mem_stable_iff b n x.val).1 x.property.1 N (by omega)
    let y := down b (n+1) N hN z
    have hy : b n y = x.val := by
      have he := down_comp b n (n+1) N (Nat.le_succ n) hN
      rw [down_adjacent] at he
      rw [he] at hz
      exact hz
    refine ⟨⟨y, ?_, ?_⟩, hy⟩
    · rw [hN' N le_rfl]; exact ⟨z,rfl⟩
    · calc
        q (n+1) y = q n (b n y) := by rw [← hq n]; rfl
        _ = c := by rw [hy]; exact x.property.2
  let chooseNext : ∀ n, S n → S (n+1) := fun n x => (lift n x).choose
  let x : ∀ n, S n := fun n => Nat.rec (Classical.choice (hn 0))
      (fun n x => chooseNext n x) n
  refine ⟨fun n => (x n).val, fun n => (x n).property.2, fun n => ?_⟩
  exact (lift n (x n)).choose_spec

end MathGauge.LinearTower
