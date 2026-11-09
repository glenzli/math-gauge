import Bounds

open scoped BigOperators ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

noncomputable section
namespace HCH02

set_option linter.unusedSectionVars false

variable {X I : Type} {bot : X} [Fintype I] [Nonempty I]

def product : List (Mat I) → Mat I
  | [] => unit
  | [M] => M
  | M :: N :: ms => mmul (product (N :: ms)) M

theorem product_cons (M : Mat I) (ms : List (Mat I)) :
    product (M :: ms) = mmul (product ms) M := by
  cases ms with
  | nil => exact (unit_mmul M).symm
  | cons N ns => rfl

theorem product_empty : product ([] : List (Mat I)) = unit := rfl
theorem product_single (M : Mat I) : product [M] = M := rfl

abbrev Step (X I : Type) (bot : X) := Operator X bot × Mat I

def chain : List (Step X I bot) → Operator X bot
  | [] => identity
  | s :: ss => compose (chain ss) s.1

def finalImage : List (Step X I bot) → Set X → Set X
  | [], U => U
  | s :: ss, U => finalImage ss (s.1.func '' U)

def inputDomain : List (Step X I bot) → Set X → ℕ → Set X
  | [], U, _ => U
  | _ :: _, U, 0 => U
  | s :: ss, U, n + 1 => inputDomain ss (s.1.func '' U) n

def Steps (R : Operator X bot → Set X → Mat I → Prop) :
    List (Step X I bot) → Set X → Prop
  | [], _ => True
  | s :: ss, U => R s.1 U s.2 ∧ Steps R ss (s.1.func '' U)

theorem chain_fold (ss : List (Step X I bot)) (x : X) :
    (chain ss).func x = ss.foldl (fun y s => s.1.func y) x := by
  induction ss generalizing x with
  | nil => rfl
  | cons s ss ih => exact ih (s.1.func x)

theorem steps_iff (R : Operator X bot → Set X → Mat I → Prop)
    (ss : List (Step X I bot)) (U : Set X) :
    Steps R ss U ↔ ∀ n (hn : n < ss.length),
      R ss[n].1 (inputDomain ss U n) ss[n].2 := by
  induction ss generalizing U with
  | nil => simp [Steps]
  | cons s ss ih =>
    constructor
    · rintro ⟨h, hs⟩ n hn
      cases n with
      | zero => exact h
      | succ n => exact (ih _).mp hs n (by simpa using hn)
    · intro h
      exact ⟨h 0 (by simp), (ih _).mpr (fun n hn => h (n + 1) (by simpa using hn))⟩

theorem image_chain (ss : List (Step X I bot)) (U : Set X) :
    (chain ss).func '' U = finalImage ss U := by
  induction ss generalizing U with
  | nil => simp [chain, identity, finalImage]
  | cons s ss ih =>
    simpa only [chain, compose, Set.image_image, finalImage] using ih (s.1.func '' U)

theorem inputDomain_prefix (ss : List (Step X I bot)) (U : Set X) (n : ℕ) :
    inputDomain ss U n = (chain (ss.take n)).func '' U := by
  induction ss generalizing U n with
  | nil => simp [inputDomain, chain, identity]
  | cons s ss ih =>
    cases n with
    | zero => simp [inputDomain, chain, identity]
    | succ n =>
      simpa only [inputDomain, List.take_succ_cons, chain, compose, Set.image_image]
        using ih (s.1.func '' U) n

theorem chain_domains (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain ss)) :
    Steps (fun φ V _ => V ⊆ dom φ) ss U := by
  induction ss generalizing U with
  | nil => trivial
  | cons s ss ih =>
    refine ⟨fun x hx => ((dom_comp _ _ x).mp (hU hx)).1, ih _ ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ((dom_comp _ _ x).mp (hU hx)).2

theorem actual_domains (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain ss)) (n : ℕ) (hn : n < ss.length) :
    inputDomain ss U n ⊆ dom ss[n].1 :=
  (steps_iff _ ss U).mp (chain_domains ss U hU) n hn

theorem lip_unit (d : I → X → X → ℝ≥0∞) (U : Set X)
    (hU : U ⊆ dom (identity : Operator X bot)) :
    unit ∈ LipOn d (identity : Operator X bot) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simp [action_unit, identity]

theorem colip_unit (d : I → X → X → ℝ≥0∞) (U : Set X)
    (hne : U.Nonempty) (hU : U ⊆ dom (identity : Operator X bot)) :
    unit ∈ CoLipOn d (identity : Operator X bot) U := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  simp [action_unit, identity]

theorem chain_lip (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain ss)) (hs : Steps (LipOn d) ss U) :
    product (ss.map Prod.snd) ∈ LipOn d (chain ss) U := by
  induction ss generalizing U with
  | nil => exact lip_unit d U hU
  | cons s ss ih =>
    have ht : s.1.func '' U ⊆ dom (chain ss) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ((dom_comp _ _ x).mp (hU hx)).2
    simpa only [List.map_cons, product_cons, chain] using
      lip_comp hU hs.1 (ih _ ht hs.2)

theorem chain_colip (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X I bot)) (U : Set X) (hne : U.Nonempty)
    (hU : U ⊆ dom (chain ss)) (hs : Steps (CoLipOn d) ss U) :
    product (ss.map Prod.snd) ∈ CoLipOn d (chain ss) U := by
  induction ss generalizing U with
  | nil => exact colip_unit d U hne hU
  | cons s ss ih =>
    have ht : s.1.func '' U ⊆ dom (chain ss) := by
      rintro _ ⟨x, hx, rfl⟩
      exact ((dom_comp _ _ x).mp (hU hx)).2
    simpa only [List.map_cons, product_cons, chain] using
      colip_comp hU hs.1 (ih _ (hne.image _) ht hs.2)

theorem nonempty_chain_colip (d : I → X → X → ℝ≥0∞)
    (s : Step X I bot) (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain (s :: ss))) (hs : Steps (CoLipOn d) (s :: ss) U) :
    product ((s :: ss).map Prod.snd) ∈ CoLipOn d (chain (s :: ss)) U :=
  chain_colip d _ U hs.1.1 hU hs

theorem finite_lip (d : I → X → X → ℝ≥0∞)
    (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain ss))
    (hs : ∀ n (hn : n < ss.length),
      ss[n].2 ∈ LipOn d ss[n].1 (inputDomain ss U n)) :
    product (ss.map Prod.snd) ∈ LipOn d (chain ss) U :=
  chain_lip d ss U hU ((steps_iff _ ss U).mpr hs)

theorem finite_colip (d : I → X → X → ℝ≥0∞)
    (s : Step X I bot) (ss : List (Step X I bot)) (U : Set X)
    (hU : U ⊆ dom (chain (s :: ss)))
    (hs : ∀ n (hn : n < (s :: ss).length),
      (s :: ss)[n].2 ∈ CoLipOn d (s :: ss)[n].1 (inputDomain (s :: ss) U n)) :
    product ((s :: ss).map Prod.snd) ∈ CoLipOn d (chain (s :: ss)) U :=
  nonempty_chain_colip d s ss U hU ((steps_iff _ (s :: ss) U).mpr hs)

/- Paths include every intermediate index, without filtering by edge weights. -/
def Paths : List (Mat I) → Type
  | [] => PUnit
  | [_] => PUnit
  | _ :: N :: ms => I × Paths (N :: ms)

def weight : (ms : List (Mat I)) → Paths ms → I → I → ℝ≥0∞
  | [], _, i, j => unit i j
  | [M], _, i, j => M i j
  | M :: N :: ms, p, i, j => weight (N :: ms) p.2 p.1 j * M i p.1

def AllPositive : (ms : List (Mat I)) → Paths ms → I → I → Prop
  | [], _, i, j => i = j
  | [M], _, i, j => 0 < M i j
  | M :: N :: ms, p, i, j => 0 < M i p.1 ∧ AllPositive (N :: ms) p.2 p.1 j

def HasZero : (ms : List (Mat I)) → Paths ms → I → I → Prop
  | [], _, i, j => i ≠ j
  | [M], _, i, j => M i j = 0
  | M :: N :: ms, p, i, j => M i p.1 = 0 ∨ HasZero (N :: ms) p.2 p.1 j

theorem paths_single (M : Mat I) : ∃ p : Paths [M], ∀ q, q = p := by
  exact ⟨PUnit.unit, fun q => by cases q; rfl⟩

theorem weight_zero (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    weight (M :: ms) p i j = 0 ↔ HasZero (M :: ms) p i j := by
  induction ms generalizing M i with
  | nil => rfl
  | cons N ns ih =>
    simp only [weight, HasZero, mul_eq_zero, ih N p.2 p.1, or_comm]

theorem weight_positive (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    0 < weight (M :: ms) p i j ↔ AllPositive (M :: ms) p i j := by
  induction ms generalizing M i with
  | nil => rfl
  | cons N ns ih =>
    simp only [weight, AllPositive, ENNReal.mul_pos_iff, ih N p.2 p.1, and_comm]

def edgeValues : (ms : List (Mat I)) → Paths ms → I → I → List ℝ≥0∞
  | [], _, _, _ => []
  | [M], _, i, j => [M i j]
  | M :: N :: ms, p, i, j => M i p.1 :: edgeValues (N :: ms) p.2 p.1 j

theorem edges_length (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    (edgeValues (M :: ms) p i j).length = ms.length + 1 := by
  induction ms generalizing M i with
  | nil => rfl
  | cons N ns ih => simp [edgeValues, ih N p.2 p.1]

theorem weight_edges (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    weight (M :: ms) p i j = (edgeValues (M :: ms) p i j).prod := by
  induction ms generalizing M i with
  | nil => simp [weight, edgeValues]
  | cons N ns ih => simp [weight, edgeValues, ih N p.2 p.1, mul_comm]

theorem positive_edges (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    AllPositive (M :: ms) p i j ↔ ∀ a ∈ edgeValues (M :: ms) p i j, 0 < a := by
  induction ms generalizing M i with
  | nil => simp [AllPositive, edgeValues]
  | cons N ns ih => simp [AllPositive, edgeValues, ih N p.2 p.1]

theorem zero_edges (M : Mat I) (ms : List (Mat I))
    (p : Paths (M :: ms)) (i j : I) :
    HasZero (M :: ms) p i j ↔ (0 : ℝ≥0∞) ∈ edgeValues (M :: ms) p i j := by
  induction ms generalizing M i with
  | nil => simp [HasZero, edgeValues, eq_comm]
  | cons N ns ih => simp [HasZero, edgeValues, ih N p.2 p.1, eq_comm]

/- Removing the head index identifies these paths with I^(length-1). -/
def finConsEquiv (n : ℕ) : I × (Fin n → I) ≃ (Fin (n + 1) → I) where
  toFun p := Fin.cases p.1 p.2
  invFun f := (f 0, fun k => f k.succ)
  left_inv p := by cases p; rfl
  right_inv f := by
    funext k
    exact Fin.cases rfl (fun _ => rfl) k

def intermediates : (M : Mat I) → (ms : List (Mat I)) → Paths (M :: ms) ≃ (Fin ms.length → I)
  | _, [] =>
    ⟨fun _ k => Fin.elim0 k, fun _ => PUnit.unit,
      (fun p => by cases p; rfl), (fun f => by funext k; exact Fin.elim0 k)⟩
  | M, N :: ns =>
    (Equiv.prodCongr (Equiv.refl I) (intermediates N ns)).trans
      (finConsEquiv ns.length)

theorem product_zero_paths (M : Mat I) (ms : List (Mat I)) (i j : I) :
    product (M :: ms) i j = 0 ↔ ∀ p, HasZero (M :: ms) p i j := by
  induction ms generalizing M i with
  | nil => simp [product, HasZero, Paths]
  | cons N ns ih =>
    simp only [product, mmul, Finset.sum_eq_zero_iff, Finset.mem_univ, forall_const,
      mul_eq_zero, ih N]
    constructor
    · intro h p
      rcases h p.1 with ht | hz
      · exact Or.inr (ht p.2)
      · exact Or.inl hz
    · intro h k
      by_cases hz : M i k = 0
      · exact Or.inr hz
      · exact Or.inl (fun p => (h (k, p)).resolve_left hz)

theorem product_positive_paths (M : Mat I) (ms : List (Mat I)) (i j : I) :
    0 < product (M :: ms) i j ↔ ∃ p, AllPositive (M :: ms) p i j := by
  induction ms generalizing M i with
  | nil => simp [product, AllPositive, Paths]
  | cons N ns ih =>
    simp only [product, mmul, Finset.sum_pos_iff, Finset.mem_univ, true_and,
      ENNReal.mul_pos_iff, ih N]
    constructor
    · rintro ⟨k, ⟨p, hp⟩, hk⟩
      exact ⟨(k, p), hk, hp⟩
    · rintro ⟨⟨k, p⟩, hk, hp⟩
      exact ⟨k, ⟨p, hp⟩, hk⟩

/- Textbook chain specialization: local certificates are the only analytic data. -/
theorem lip_chain_zero_paths (d : I → X → X → ℝ≥0∞)
    (s : Step X I bot) (ss : List (Step X I bot)) (U : Set X)
    (_hU : U ⊆ dom (chain (s :: ss)))
    (_hs : Steps (LipOn d) (s :: ss) U) (i j : I) :
    product (s.2 :: ss.map Prod.snd) i j = 0 ↔
      ∀ p, HasZero (s.2 :: ss.map Prod.snd) p i j :=
  product_zero_paths _ _ i j

theorem colip_chain_positive_paths (d : I → X → X → ℝ≥0∞)
    (s : Step X I bot) (ss : List (Step X I bot)) (U : Set X)
    (_hU : U ⊆ dom (chain (s :: ss)))
    (_hs : Steps (CoLipOn d) (s :: ss) U) (i j : I) :
    0 < product (s.2 :: ss.map Prod.snd) i j ↔
      ∃ p, AllPositive (s.2 :: ss.map Prod.snd) p i j :=
  product_positive_paths _ _ i j

end HCH02
