import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace MathGauge.F110

variable {Y : Type*} [DecidableEq Y]

def layers (B : Finset Y) (g : Y → Y) : ℕ → Finset Y
  | 0 => B
  | n + 1 => B.filter (fun y => g y ∈ layers B g n)

theorem layers_decreasing (B : Finset Y) (g : Y → Y) (n : ℕ) :
    layers B g (n + 1) ⊆ layers B g n := by
  induction n with
  | zero =>
      exact Finset.filter_subset _ _
  | succ n ih =>
      intro y hy
      rcases Finset.mem_filter.mp hy with ⟨hB, hg⟩
      exact Finset.mem_filter.mpr ⟨hB, ih hg⟩

theorem layers_subset (B : Finset Y) (g : Y → Y) (n : ℕ) :
    layers B g n ⊆ B := by
  cases n with
  | zero =>
      exact fun _ h => h
  | succ n =>
      exact Finset.filter_subset _ _

theorem layers_stable_tail (B : Finset Y) (g : Y → Y) {m : ℕ}
    (hm : layers B g (m + 1) = layers B g m) (k : ℕ) :
    layers B g (m + k) = layers B g m := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        layers B g (m + (k + 1)) =
            B.filter (fun y => g y ∈ layers B g (m + k)) := rfl
        _ = B.filter (fun y => g y ∈ layers B g m) := by
          rw [ih]
        _ = layers B g m := hm

theorem layers_stabilize (B : Finset Y) (g : Y → Y) :
    layers B g (B.card + 1) = layers B g B.card := by
  obtain ⟨m, hm, heq⟩ :
      ∃ m ≤ B.card, layers B g (m + 1) = layers B g m := by
    by_contra h
    have hne : ∀ n, n ≤ B.card →
        layers B g (n + 1) ≠ layers B g n := by
      intro n hn he
      exact h ⟨n, hn, he⟩
    have hbound :
        ∀ n ≤ B.card + 1, (layers B g n).card + n ≤ B.card := by
      intro n
      induction n with
      | zero =>
          intro hn
          simp [layers]
      | succ n ih =>
          intro hn
          have hn' : n ≤ B.card := by omega
          have hi := ih (by omega : n ≤ B.card + 1)
          have hlt :
              (layers B g (n + 1)).card < (layers B g n).card :=
            Finset.card_lt_card
              ⟨layers_decreasing B g n,
                fun hs =>
                  hne n hn'
                    (Finset.Subset.antisymm
                      (layers_decreasing B g n) hs)⟩
          omega
    have hbad := hbound (B.card + 1) le_rfl
    omega
  have h₀ := layers_stable_tail B g heq (B.card - m)
  have h₁ := layers_stable_tail B g heq (B.card + 1 - m)
  rw [Nat.add_sub_of_le hm] at h₀
  rw [Nat.add_sub_of_le (by omega : m ≤ B.card + 1)] at h₁
  exact h₁.trans h₀.symm

def terminal (B : Finset Y) (g : Y → Y) : Finset Y :=
  layers B g B.card

theorem terminal_mem (B : Finset Y) (g : Y → Y) (y : Y) :
    y ∈ terminal B g ↔ y ∈ B ∧ g y ∈ terminal B g := by
  have h := layers_stabilize B g
  change y ∈ layers B g B.card ↔
    y ∈ B ∧ g y ∈ layers B g B.card
  constructor
  · intro hy
    have hn : y ∈ layers B g (B.card + 1) := by
      rw [h]
      exact hy
    change y ∈ B.filter (fun z => g z ∈ layers B g B.card) at hn
    exact Finset.mem_filter.mp hn
  · intro hy
    have hn : y ∈ layers B g (B.card + 1) := by
      change y ∈ B.filter (fun z => g z ∈ layers B g B.card)
      exact Finset.mem_filter.mpr hy
    rw [h] at hn
    exact hn

end MathGauge.F110
