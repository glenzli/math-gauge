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
namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open Set

theorem covering_number_image_eq_of_isometric_embedding
    {X Y : Type} (dX : X → X → ENNReal) (dY : Y → Y → ENNReal)
    (e : X → Y) (U : Set X) (ε : ENNReal)
    (hinj : Set.InjOn e U)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, dY (e x) (e y) = dX x y) :
    covering_number dY ε (e '' U) = covering_number dX ε U := by
  classical
  apply le_antisymm
  · by_cases hfin : ∃ S : Finset X, InternalEpsilonNet dX ε U S
    · obtain ⟨S, hS, hcover, _⟩ := covering_number_attained dX ε U hfin
      have hSimg : InternalEpsilonNet dY ε (e '' U) (S.image e) := by
        constructor
        · intro z hz
          rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
          exact ⟨s, hS.1 hs, rfl⟩
        · intro z hz
          rcases hz with ⟨x, hx, rfl⟩
          rcases hS.2 x hx with ⟨s, hs, hdist⟩
          refine ⟨e s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
          rwa [hiso x hx s (hS.1 hs)]
      calc
        covering_number dY ε (e '' U) ≤ ((S.image e).card : ENNReal) :=
          covering_number_le_card_of_net hSimg
        _ = (S.card : ENNReal) := by
          rw [Finset.card_image_of_injOn]
          intro a ha b hb hab
          exact hinj (hS.1 ha) (hS.1 hb) hab
        _ = covering_number dX ε U := hcover.symm
    · have hno : ¬ ∃ T : Finset Y, InternalEpsilonNet dY ε (e '' U) T := by
        rintro ⟨T, hT⟩
        let rep : {t : Y // t ∈ T} → X := fun t =>
          Classical.choose (hT.1 t.2)
        have hrepU : ∀ t : {t : Y // t ∈ T}, rep t ∈ U := fun t =>
          (Classical.choose_spec (hT.1 t.2)).1
        have hrepval : ∀ t : {t : Y // t ∈ T}, e (rep t) = t.1 := fun t =>
          (Classical.choose_spec (hT.1 t.2)).2
        let S : Finset X := T.attach.image rep
        have hS : InternalEpsilonNet dX ε U S := by
          constructor
          · intro x hx
            rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
            exact hrepU t
          · intro x hx
            rcases hT.2 (e x) ⟨x, hx, rfl⟩ with ⟨t, ht, hdist⟩
            refine ⟨rep ⟨t, ht⟩, ?_, ?_⟩
            · exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩
            · have hdist' : dY (e x) (e (rep ⟨t, ht⟩)) < ε := by
                simpa [hrepval ⟨t, ht⟩] using hdist
              simpa [hiso x hx (rep ⟨t, ht⟩) (hrepU ⟨t, ht⟩)] using hdist'
        exact hfin ⟨S, hS⟩
      rw [(covering_number_eq_top_iff dY ε (e '' U)).mpr hno,
        (covering_number_eq_top_iff dX ε U).mpr hfin]
  · by_cases hfin : ∃ T : Finset Y, InternalEpsilonNet dY ε (e '' U) T
    · obtain ⟨T, hT, hcover, _⟩ := covering_number_attained dY ε (e '' U) hfin
      let rep : {t : Y // t ∈ T} → X := fun t =>
        Classical.choose (hT.1 t.2)
      have hrepU : ∀ t : {t : Y // t ∈ T}, rep t ∈ U := fun t =>
        (Classical.choose_spec (hT.1 t.2)).1
      have hrepval : ∀ t : {t : Y // t ∈ T}, e (rep t) = t.1 := fun t =>
        (Classical.choose_spec (hT.1 t.2)).2
      let S : Finset X := T.attach.image rep
      have hS : InternalEpsilonNet dX ε U S := by
        constructor
        · intro x hx
          rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
          exact hrepU t
        · intro x hx
          rcases hT.2 (e x) ⟨x, hx, rfl⟩ with ⟨t, ht, hdist⟩
          refine ⟨rep ⟨t, ht⟩, ?_, ?_⟩
          · exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩
          · have hdist' : dY (e x) (e (rep ⟨t, ht⟩)) < ε := by
              simpa [hrepval ⟨t, ht⟩] using hdist
            simpa [hiso x hx (rep ⟨t, ht⟩) (hrepU ⟨t, ht⟩)] using hdist'
      calc
        covering_number dX ε U ≤ (S.card : ENNReal) := covering_number_le_card_of_net hS
        _ ≤ (T.card : ENNReal) := by
          exact_mod_cast (by
            calc
              S.card ≤ T.attach.card := Finset.card_image_le
              _ = T.card := Finset.card_attach)
        _ = covering_number dY ε (e '' U) := hcover.symm
    · rw [(covering_number_eq_top_iff dX ε U).mpr (by
        intro hU
        obtain ⟨S, hS⟩ := hU
        let T : Finset Y := S.image e
        have hT : InternalEpsilonNet dY ε (e '' U) T := by
          constructor
          · intro z hz
            rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
            exact ⟨s, hS.1 hs, rfl⟩
          · intro z hz
            rcases hz with ⟨x, hx, rfl⟩
            rcases hS.2 x hx with ⟨s, hs, hdist⟩
            refine ⟨e s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
            rwa [hiso x hx s (hS.1 hs)]
        exact hfin ⟨T, hT⟩),
        (covering_number_eq_top_iff dY ε (e '' U)).mpr hfin]

theorem realU35_cover_eq : covering_number lineDist sevenQuarters realU35 = 2 := by
  have h := covering_number_image_eq_of_isometric_embedding d4 lineDist e35
    (Set.univ : Set (Fin 4)) sevenQuarters
    (by
      intro x _ y _ hxy
      exact e35_injective hxy)
    (by intro x _ y _; exact e35_isometry x y)
  rw [← e35_image, h]
  simpa [U4] using U4_cover_sevenQuarters

end formal_oet.vol_01.ch_03_operator_local_degeneracy
namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open Set

theorem fReal35_image : fReal35 '' realU35 = realU35 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa [fReal35] using hx
  · intro hy
    exact ⟨y, hy, by simp [fReal35]⟩

theorem gReal35_image : gReal35 '' realU35 = realU35 := by
  rw [← e35_image]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases hx with ⟨i, -, rfl⟩
    exact ⟨g4 i, by simp, e35_comm_g i⟩
  · rintro ⟨i, -, rfl⟩
    have hi : i ∈ g4 '' U4 := by
      rw [g4_image]; simp [U4]
    obtain ⟨j, -, hji⟩ := (show i ∈ Set.image g4 (Set.univ : Set (Fin 4)) from by simpa [U4, Set.image_univ] using hi)
    refine ⟨e35 j, ⟨j, by simp, rfl⟩, ?_⟩
    rw [← e35_comm_g j, hji]

theorem fReal35_cover : covering_number lineDist sevenQuarters (fReal35 '' realU35) = 2 := by
  rw [fReal35_image]
  exact realU35_cover_eq

theorem gReal35_cover : covering_number lineDist sevenQuarters (gReal35 '' realU35) = 2 := by
  rw [gReal35_image]
  exact realU35_cover_eq

def RealFuncLip (f : Option ℝ → Option ℝ) (U : Set (Option ℝ)) (L : ENNReal) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, lineDist (f x) (f y) ≤ L * lineDist x y

theorem fReal35_lip_one : RealFuncLip fReal35 realU35 1 := by
  intro x hx y hy
  have hx' : x ∈ e35 '' (Set.univ : Set (Fin 4)) := by
    rw [e35_image]; exact hx
  have hy' : y ∈ e35 '' (Set.univ : Set (Fin 4)) := by
    rw [e35_image]; exact hy
  rcases hx' with ⟨i, -, rfl⟩
  rcases hy' with ⟨j, -, rfl⟩
  simpa [fReal35, f4, e35_isometry] using f4_lip_one i (by simp) j (by simp)

theorem gReal35_lip_three : RealFuncLip gReal35 realU35 3 := by
  intro x hx y hy
  have hx' : x ∈ e35 '' (Set.univ : Set (Fin 4)) := by
    rw [e35_image]; exact hx
  have hy' : y ∈ e35 '' (Set.univ : Set (Fin 4)) := by
    rw [e35_image]; exact hy
  rcases hx' with ⟨i, -, rfl⟩
  rcases hy' with ⟨j, -, rfl⟩
  rw [← e35_comm_g i, ← e35_comm_g j]
  simpa [e35_isometry] using g4_lip_three i (by simp) j (by simp)

theorem fReal35_lip_min : ∀ L : ENNReal, RealFuncLip fReal35 realU35 L → (1 : ENNReal) ≤ L := by
  intro L hL
  have h := hL (e35 0) (by simp [realU35, e35])
    (e35 1) (by simp [realU35, e35])
  simpa [fReal35, f4, e35_isometry, d4] using h

theorem gReal35_lip_min : ∀ L : ENNReal, RealFuncLip gReal35 realU35 L → (3 : ENNReal) ≤ L := by
  intro L hL
  have h := hL (e35 0) (by simp [realU35, e35])
    (e35 1) (by simp [realU35, e35])
  rw [← e35_comm_g 0, ← e35_comm_g 1] at h
  simpa [e35_isometry, d4, g4] using h

theorem fReal35_entropy_diff_zero :
    FuncEntropyDiff lineDist fReal35 realU35 sevenQuarters = 0 := by
  unfold FuncEntropyDiff
  rw [fReal35_image]
  exact erealSub_self _

theorem gReal35_entropy_diff_zero :
    FuncEntropyDiff lineDist gReal35 realU35 sevenQuarters = 0 := by
  unfold FuncEntropyDiff
  rw [gReal35_image]
  exact erealSub_self _

theorem realU35_cover_sevenTwelfths :
    covering_number lineDist sevenTwelfths realU35 = 4 := by
  have h := covering_number_image_eq_of_isometric_embedding d4 lineDist e35
    (Set.univ : Set (Fin 4)) sevenTwelfths
    (by
      intro x _ y _ hxy
      exact e35_injective hxy)
    (by intro x _ y _; exact e35_isometry x y)
  rw [← e35_image, h]
  simpa [U4] using U4_cover_sevenTwelfths

theorem ex35_real_model_comparison :
    covering_number lineDist sevenTwelfths realU35 = 4 ∧
    covering_number lineDist sevenQuarters realU35 = 2 ∧
    covering_number lineDist sevenQuarters (fReal35 '' realU35) = 2 ∧
    covering_number lineDist sevenQuarters (gReal35 '' realU35) = 2 ∧
    covering_number lineDist sevenQuarters (fReal35 '' realU35) ≤
      covering_number lineDist sevenQuarters realU35 ∧
    covering_number lineDist sevenQuarters (gReal35 '' realU35) ≤
      covering_number lineDist sevenTwelfths realU35 ∧
    RealFuncLip fReal35 realU35 1 ∧
    RealFuncLip gReal35 realU35 3 ∧
    (∀ L : ENNReal, RealFuncLip fReal35 realU35 L → (1 : ENNReal) ≤ L) ∧
    (∀ L : ENNReal, RealFuncLip gReal35 realU35 L → (3 : ENNReal) ≤ L) ∧
    FuncEntropyDiff lineDist fReal35 realU35 sevenQuarters = 0 ∧
    FuncEntropyDiff lineDist gReal35 realU35 sevenQuarters = 0 := by
  refine ⟨realU35_cover_sevenTwelfths, realU35_cover_eq, fReal35_cover, gReal35_cover,
    ?_, ?_, fReal35_lip_one, gReal35_lip_three, fReal35_lip_min, gReal35_lip_min,
    fReal35_entropy_diff_zero, gReal35_entropy_diff_zero⟩
  · rw [fReal35_cover, realU35_cover_eq]
  · rw [gReal35_cover, realU35_cover_sevenTwelfths]
    norm_num

end formal_oet.vol_01.ch_03_operator_local_degeneracy
