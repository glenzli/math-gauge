import CH03.Exercises

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open Set

set_option maxHeartbeats 8000000

/-- Four-point model of the unit-spaced set `{0,1,2,3}`. -/
def d4 (x y : Fin 4) : ENNReal :=
  ((if x.val ≤ y.val then y.val - x.val else x.val - y.val : ℕ) : ENNReal)

theorem d4_symm (x y : Fin 4) : d4 x y = d4 y x := by
  fin_cases x <;> fin_cases y <;> norm_num [d4]

theorem d4_triangle (x y z : Fin 4) : d4 x z ≤ d4 x y + d4 y z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> norm_num [d4]

def f4 (x : Fin 4) : Fin 4 := x
def g4 (x : Fin 4) : Fin 4 := ![0, 3, 1, 2] x
def U4 : Set (Fin 4) := Set.univ

@[simp] theorem mem_U4 (x : Fin 4) : x ∈ U4 := by simp [U4]

theorem d4_lt_one_eq {x y : Fin 4} (h : d4 x y < (1 : ENNReal)) : x = y := by
  fin_cases x <;> fin_cases y <;> simp [d4] at h ⊢
  all_goals exact (not_lt_of_ge (by norm_num : (2 : ENNReal) ≤ 3)) h <;> omega

theorem d4_lt_two_eq_or {x y : Fin 4} (h : d4 x y < (2 : ENNReal)) :
    d4 x y = 0 ∨ d4 x y = 1 := by
  fin_cases x <;> fin_cases y <;> simp [d4] at h ⊢
  all_goals exact (not_lt_of_ge (by norm_num : (2 : ENNReal) ≤ 3)) h

theorem U4_cover_four {ε : ENNReal} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    covering_number d4 ε U4 = 4 := by
  have hnet : InternalEpsilonNet d4 ε U4 (Finset.univ : Finset (Fin 4)) := by
    constructor
    · intro x hx; simp
    · intro x hx
      refine ⟨x, by simp, ?_⟩
      have : d4 x x = 0 := by simp [d4]
      rw [this]
      exact hε0
  apply le_antisymm
  · calc
      covering_number d4 ε U4 ≤ ((Finset.univ : Finset (Fin 4)).card : ENNReal) :=
        covering_number_le_card_of_net hnet
      _ = 4 := by simp
  · by_contra hnot
    have hlt : covering_number d4 ε U4 < (4 : ENNReal) := lt_of_not_ge hnot
    have hfin : ∃ S : Finset (Fin 4), InternalEpsilonNet d4 ε U4 S :=
      ⟨Finset.univ, hnet⟩
    obtain ⟨S, hS, hcover, hmin⟩ := covering_number_attained d4 ε U4 hfin
    have hsub : (Finset.univ : Finset (Fin 4)) ⊆ S := by
      intro x _
      rcases hS.2 x (by simp) with ⟨c, hc, hdist⟩
      have hcx : c = x := by
        symm
        exact d4_lt_one_eq (lt_of_lt_of_le hdist hε1)
      simpa [hcx] using hc
    have hcard : (4 : ℕ) ≤ S.card := by
      simpa using Finset.card_le_card hsub
    have : (4 : ENNReal) ≤ covering_number d4 ε U4 := by
      rw [hcover]
      exact_mod_cast hcard
    exact (not_lt_of_ge this) hlt

theorem no_single_cover_two (c : Fin 4) :
    ∃ x : Fin 4, ¬ d4 x c < (2 : ENNReal) := by
  fin_cases c
  · exact ⟨3, by norm_num [d4]⟩
  · exact ⟨3, by norm_num [d4]⟩
  · exact ⟨0, by norm_num [d4]⟩
  · exact ⟨0, by norm_num [d4]⟩

theorem U4_cover_two {ε : ENNReal} (hε0 : 0 < ε) (hε1 : 1 < ε) (hε2 : ε ≤ 2) :
    covering_number d4 ε U4 = 2 := by
  have hnet : InternalEpsilonNet d4 ε U4 ({1, 3} : Finset (Fin 4)) := by
    constructor
    · intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> simp
    · intro x hx
      fin_cases x
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact hε1
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact hε0
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact hε1
      · refine ⟨3, by simp, ?_⟩
        norm_num [d4]
        exact hε0
  apply le_antisymm
  · calc
      covering_number d4 ε U4 ≤ (({1, 3} : Finset (Fin 4)).card : ENNReal) :=
        covering_number_le_card_of_net hnet
      _ = 2 := by simp
  · by_contra hnot
    have hlt : covering_number d4 ε U4 < (2 : ENNReal) := lt_of_not_ge hnot
    have hfin : ∃ S : Finset (Fin 4), InternalEpsilonNet d4 ε U4 S :=
      ⟨{1, 3}, hnet⟩
    obtain ⟨S, hS, hcover, hmin⟩ := covering_number_attained d4 ε U4 hfin
    have hcardlt : S.card < 2 := by
      have : (S.card : ENNReal) < (2 : ENNReal) := by
        rw [← hcover]; exact hlt
      exact_mod_cast this
    have hle : S.card ≤ 1 := by omega
    have hall := Finset.card_le_one.mp hle
    rcases hS.2 0 (by simp) with ⟨c0, hc0, _⟩
    have hcov : ∀ x : Fin 4, d4 x c0 < ε := by
      intro x
      rcases hS.2 x (by simp) with ⟨c, hc, hdist⟩
      have hcc0 : c = c0 := hall c hc c0 hc0
      simpa [hcc0] using hdist
    rcases no_single_cover_two c0 with ⟨x, hnotlt⟩
    exact hnotlt (lt_of_lt_of_le (hcov x) hε2)

theorem U4_cover_one {ε : ENNReal} (hε2 : 2 < ε) :
    covering_number d4 ε U4 = 1 := by
  have hnet : InternalEpsilonNet d4 ε U4 ({1} : Finset (Fin 4)) := by
    constructor
    · intro x hx; simp at hx; subst x; simp
    · intro x hx
      fin_cases x
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact lt_trans (by norm_num : (1:ENNReal) < 2) hε2
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact lt_trans (by norm_num : (0:ENNReal) < 2) hε2
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact lt_trans (by norm_num : (1:ENNReal) < 2) hε2
      · refine ⟨1, by simp, ?_⟩
        norm_num [d4]
        exact hε2
  apply le_antisymm
  · calc
      covering_number d4 ε U4 ≤ (({1} : Finset (Fin 4)).card : ENNReal) :=
        covering_number_le_card_of_net hnet
      _ = 1 := by simp
  · exact one_le_covering_number_of_nonempty d4 ε U4 ⟨0, by simp⟩

theorem f4_image : f4 '' U4 = U4 := by
  ext x; simp [f4, U4]

theorem g4_image : g4 '' U4 = U4 := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩
    fin_cases y <;> simp [g4]
  · intro hx
    fin_cases x
    · refine ⟨0, by simp, ?_⟩; decide
    · refine ⟨2, by simp, ?_⟩; decide
    · refine ⟨3, by simp, ?_⟩; decide
    · refine ⟨1, by simp, ?_⟩; decide

noncomputable def sevenQuarters : ENNReal := ((7/4 : NNReal) : ENNReal)
noncomputable def sevenTwelfths : ENNReal := ((7/12 : NNReal) : ENNReal)

theorem one_lt_sevenQuarters : (1 : ENNReal) < sevenQuarters := by
  unfold sevenQuarters
  exact_mod_cast (by norm_num : (1 : NNReal) < 7/4)

theorem sevenQuarters_le_two : sevenQuarters ≤ (2 : ENNReal) := by
  unfold sevenQuarters
  change ((7/4 : NNReal) : ENNReal) ≤ ((2 : NNReal) : ENNReal)
  exact_mod_cast (by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 4)]
    norm_num : (7/4 : NNReal) ≤ 2)

theorem sevenTwelfths_le_one : sevenTwelfths ≤ (1 : ENNReal) := by
  unfold sevenTwelfths
  change ((7/12 : NNReal) : ENNReal) ≤ ((1 : NNReal) : ENNReal)
  exact_mod_cast (by
    rw [div_le_iff₀ (by norm_num : (0 : NNReal) < 12)]
    norm_num : (7/12 : NNReal) ≤ 1)

theorem zero_lt_sevenTwelfths : (0 : ENNReal) < sevenTwelfths := by
  unfold sevenTwelfths
  exact_mod_cast (by norm_num : (0 : NNReal) < 7/12)

theorem U4_cover_sevenQuarters : covering_number d4 sevenQuarters U4 = 2 := by
  apply U4_cover_two
  · exact lt_trans zero_lt_one one_lt_sevenQuarters
  · exact one_lt_sevenQuarters
  · exact sevenQuarters_le_two

theorem f4_cover_sevenQuarters : covering_number d4 sevenQuarters (f4 '' U4) = 2 := by
  rw [f4_image]; exact U4_cover_sevenQuarters

theorem g4_cover_sevenQuarters : covering_number d4 sevenQuarters (g4 '' U4) = 2 := by
  rw [g4_image]; exact U4_cover_sevenQuarters

/-- Scalar Lip certificate for a plain function. -/
def FuncLip (d : X → X → ENNReal) (f : X → X) (U : Set X) (L : ENNReal) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, d (f x) (f y) ≤ L * d x y

theorem f4_lip_one : FuncLip d4 f4 U4 1 := by
  intro x hx y hy
  simp [f4]

theorem g4_lip_three : FuncLip d4 g4 U4 3 := by
  intro x hx y hy
  fin_cases x <;> fin_cases y <;> norm_num [d4, g4]

theorem f4_lip_min : ∀ L : ENNReal, FuncLip d4 f4 U4 L → (1 : ENNReal) ≤ L := by
  intro L hL
  have h := hL 0 (by simp) 1 (by simp)
  simpa [d4, f4] using h

theorem g4_lip_min : ∀ L : ENNReal, FuncLip d4 g4 U4 L → (3 : ENNReal) ≤ L := by
  intro L hL
  have h := hL 0 (by simp) 1 (by simp)
  simpa [d4, g4] using h

theorem U4_cover_sevenTwelfths : covering_number d4 sevenTwelfths U4 = 4 := by
  exact U4_cover_four zero_lt_sevenTwelfths sevenTwelfths_le_one

noncomputable def FuncEntropyDiff (d : X → X → ENNReal) (f : X → X)
    (U : Set X) (ε : ENNReal) : EReal :=
  erealSub (metric_entropy d ε U) (metric_entropy d ε (f '' U))

theorem f4_entropy_diff_zero : FuncEntropyDiff d4 f4 U4 sevenQuarters = 0 := by
  unfold FuncEntropyDiff
  rw [f4_image]
  exact erealSub_self _

theorem g4_entropy_diff_zero : FuncEntropyDiff d4 g4 U4 sevenQuarters = 0 := by
  unfold FuncEntropyDiff
  rw [g4_image]
  exact erealSub_self _

theorem ex35_lip_cover_comparison :
    covering_number d4 sevenQuarters (f4 '' U4) ≤
        covering_number d4 sevenQuarters U4 ∧
      covering_number d4 sevenQuarters (g4 '' U4) ≤
        covering_number d4 sevenTwelfths U4 ∧
      covering_number d4 sevenQuarters (f4 '' U4) = 2 ∧
      covering_number d4 sevenQuarters (g4 '' U4) = 2 ∧
      covering_number d4 sevenTwelfths U4 = 4 := by
  refine ⟨?_, ?_, f4_cover_sevenQuarters, g4_cover_sevenQuarters, U4_cover_sevenTwelfths⟩
  · rw [f4_cover_sevenQuarters, U4_cover_sevenQuarters]
  · rw [g4_cover_sevenQuarters, U4_cover_sevenTwelfths]
    norm_num

end formal_oet.vol_01.ch_03_operator_local_degeneracy
namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open Set

def e35 (i : Fin 4) : Option ℝ := some (i.val : ℝ)

def realU35 : Set (Option ℝ) := {some (0:ℝ), some 1, some 2, some 3}

def fReal35 : Option ℝ → Option ℝ := id

noncomputable def gReal35 : Option ℝ → Option ℝ
  | none => none
  | some x =>
      if x = 0 then some 0
      else if x = 1 then some 3
      else if x = 2 then some 1
      else if x = 3 then some 2
      else none

theorem e35_injective : Function.Injective e35 := by
  intro x y h
  have hv : (x.val : ℝ) = y.val := by
    simpa [e35] using Option.some.inj h
  apply Fin.ext
  exact_mod_cast hv

theorem e35_image : e35 '' (Set.univ : Set (Fin 4)) = realU35 := by
  ext z
  constructor
  · rintro ⟨i, -, rfl⟩
    fin_cases i <;> simp [e35, realU35]
  · intro hz
    simp only [realU35, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact ⟨0, by simp, by simp [e35]⟩
    · exact ⟨1, by simp, by simp [e35]⟩
    · exact ⟨2, by simp, by simp [e35]⟩
    · exact ⟨3, by simp, by simp [e35]⟩

theorem e35_isometry (x y : Fin 4) :
    lineDist (e35 x) (e35 y) = d4 x y := by
  fin_cases x <;> fin_cases y <;> norm_num [e35, lineDist, d4]

theorem e35_comm_f : ∀ x : Fin 4, e35 (f4 x) = fReal35 (e35 x) := by
  intro x; simp [f4, fReal35, e35]

theorem e35_comm_g : ∀ x : Fin 4, e35 (g4 x) = gReal35 (e35 x) := by
  intro x
  fin_cases x <;> simp [g4, gReal35, e35]

theorem three_halves_not_in_realU35 :
    some ((3/2 : ℝ)) ∉ realU35 := by
  simp [realU35]
  norm_num

theorem ex35_finite_model_alignment :
    Function.Injective e35 ∧
      e35 '' (Set.univ : Set (Fin 4)) = realU35 ∧
      (∀ x y : Fin 4, lineDist (e35 x) (e35 y) = d4 x y) ∧
      (∀ x : Fin 4, e35 (f4 x) = fReal35 (e35 x)) ∧
      (∀ x : Fin 4, e35 (g4 x) = gReal35 (e35 x)) ∧
      some ((3/2 : ℝ)) ∉ realU35 :=
  ⟨e35_injective, e35_image, e35_isometry, e35_comm_f, e35_comm_g,
    three_halves_not_in_realU35⟩

end formal_oet.vol_01.ch_03_operator_local_degeneracy
