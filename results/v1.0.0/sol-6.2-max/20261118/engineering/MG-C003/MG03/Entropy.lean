import MG03.Radius
import Mathlib.Data.EReal.Operations

namespace MG03

open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X} {d : I → X → X → ENNReal}
variable {e eIn eOut : X → X → ENNReal} {f : Operator X bot} {A B U : Set X}
variable {r eps : ENNReal}

theorem net_iff_balls (S : Finset X) :
    InternalEpsilonNet e r U S ↔ (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ s ∈ S, ball e s r := by
  simp [InternalEpsilonNet, Set.subset_def, ball]

theorem cover_le_card {S : Finset X} (hS : InternalEpsilonNet e r U S) :
    covering_number e r U ≤ (S.card : ENNReal) :=
  iInf_le_of_le S (iInf_le_of_le hS le_rfl)

theorem le_cover_of_le_cards {c : ENNReal}
    (h : ∀ S : Finset X, InternalEpsilonNet e r U S → c ≤ (S.card : ENNReal)) :
    c ≤ covering_number e r U :=
  le_iInf fun S => le_iInf (h S)

theorem finite_self_net (he : ∀ x, e x x = 0) (hr : 0 < r) (S : Finset X) :
    InternalEpsilonNet e r (↑S : Set X) S :=
  ⟨Subset.rfl, fun x hx => ⟨x, hx, by rwa [he]⟩⟩

def HasFiniteCovers (e : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r, FiniteRadius r → covering_number e r U < ⊤

theorem hasFiniteCovers_iff :
    HasFiniteCovers e U ↔ ∀ r, FiniteRadius r → ∃ S : Finset X, InternalEpsilonNet e r U S := by
  classical
  constructor
  · intro h r hr
    exact not_not.mp ((covering_number_eq_top_iff e r U).not.mp (h r hr).ne)
  · intro h r hr
    exact lt_top_iff_ne_top.mpr ((covering_number_eq_top_iff e r U).not.mpr (not_not.mpr (h r hr)))

theorem finite_hasFiniteCovers (he : ∀ x, e x x = 0) (hU : U.Finite) : HasFiniteCovers e U := by
  classical
  apply hasFiniteCovers_iff.mpr
  intro r hr
  let S := hU.toFinset
  have hc : (↑S : Set X) = U := Set.Finite.coe_toFinset hU
  exact ⟨S, hc ▸ finite_self_net he hr.1 S⟩

theorem subfamily_dist_max [Finite I] {J : Set I} (hJ : J.Nonempty) (x y : X) :
    ∃ j : J, subfamily_pseudometric d J x y = d j.1 x y ∧ ∀ k : J, d k.1 x y ≤ d j.1 x y := by
  classical
  letI : Nonempty J := hJ.to_subtype
  letI : Fintype J := Fintype.ofFinite J
  obtain ⟨j, _, hj⟩ :=
    Finset.exists_max_image Finset.univ (fun k : J => d k.1 x y) Finset.univ_nonempty
  have h : ∀ k : J, d k.1 x y ≤ d j.1 x y := fun k => hj k (Finset.mem_univ k)
  exact ⟨j, le_antisymm (iSup_le h) (le_iSup (fun k : J => d k.1 x y) j), h⟩

noncomputable def subfamilyCover (d : I → X → X → ENNReal) (J : Set I)
    (r : ENNReal) (U : Set X) : ENNReal :=
  covering_number (subfamily_pseudometric d J) r U

theorem subfamilyCover_singleton (i : I) :
    subfamilyCover d {i} r U = covering_number (d i) r U := by
  unfold subfamilyCover
  rw [subfamily_pseudometric_singleton]

theorem subfamilyEntropy_eq_log (J : Set I) :
    subfamily_metric_entropy d J r U = log2_ereal (subfamilyCover d J r U) := rfl

theorem log2_mono : Monotone log2_ereal := by
  intro a b hab
  by_cases ha : a = 0
  · simp [ha, log2_ereal]
  by_cases hb : b = ⊤
  · simp [hb, log2_ereal]
  have hb₀ : b ≠ 0 := fun h => ha (le_antisymm (hab.trans_eq h) (zero_le _))
  have haₜ : a ≠ ⊤ := fun h => hb (top_unique (h ▸ hab))
  simp only [log2_ereal, if_neg ha, if_neg hb₀, if_neg haₜ, if_neg hb, EReal.coe_le_coe_iff]
  exact Real.logb_le_logb_of_le one_lt_two (ENNReal.toReal_pos ha haₜ)
    (ENNReal.toReal_mono hb hab)

theorem entropy_coe (hU : U.Nonempty) (h : covering_number e r U < ⊤) :
    metric_entropy e r U = (Real.logb 2 (covering_number e r U).toReal : ℝ) := by
  have hpos := zero_lt_one.trans_le (one_le_covering_number_of_nonempty e r U hU)
  simp [metric_entropy, log2_ereal, ne_of_gt hpos, h.ne]

theorem entropy_top (h : covering_number e r U = ⊤) :
    metric_entropy e r U = ⊤ := by
  simp [metric_entropy, log2_ereal, h]

theorem entropy_ne_bot (hU : U.Nonempty) : metric_entropy e r U ≠ ⊥ :=
  ne_of_gt ((show (⊥ : EReal) < 0 by simp).trans_le (metric_entropy_nonneg e r U hU))

theorem entropy_ne_top_iff (hU : U.Nonempty) :
    metric_entropy e r U ≠ ⊤ ↔ covering_number e r U < ⊤ := by
  constructor
  · exact fun h => lt_top_iff_ne_top.mpr fun hc => h (entropy_top hc)
  · intro h
    rw [entropy_coe hU h]
    exact EReal.coe_ne_top _

theorem cover_one_of_close (hU : U.Nonempty)
    (h : ∀ x ∈ U, ∀ y ∈ U, e x y < r) : covering_number e r U = 1 := by
  classical
  obtain ⟨c, hc⟩ := hU
  have hn : InternalEpsilonNet e r U {c} := by
    refine ⟨?_, fun x hx => ⟨c, Finset.mem_singleton_self c, h x hx c hc⟩⟩
    simpa only [Finset.coe_singleton, Set.singleton_subset_iff] using hc
  exact le_antisymm (by simpa using cover_le_card hn)
    (one_le_covering_number_of_nonempty e r U ⟨c, hc⟩)

theorem separated_finset_cover (he : ∀ x, e x x = 0) (hr : 0 < r) (S : Finset X)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → r ≤ e x y) :
    covering_number e r (↑S : Set X) = S.card := by
  apply le_antisymm (cover_le_card (finite_self_net he hr S))
  apply le_cover_of_le_cards
  intro T hT
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro x hx
  obtain ⟨y, hy, hxy⟩ := hT.2 x hx
  have heq : x = y := by
    by_contra hne
    exact (not_lt_of_ge (hsep x hx y (hT.1 hy) hne)) hxy
  exact heq ▸ hy

theorem two_le_cover (hU : U.Nonempty)
    (h : ∀ c ∈ U, ∃ x ∈ U, r ≤ e x c) : (2 : ENNReal) ≤ covering_number e r U := by
  apply le_cover_of_le_cards
  intro T hT
  have hcard : 2 ≤ T.card := by
    obtain ⟨y, hy⟩ := hU
    obtain ⟨c, hc, _⟩ := hT.2 y hy
    by_contra hn
    have hp := Finset.card_pos.mpr ⟨c, hc⟩
    have h1 : T.card = 1 := by omega
    obtain ⟨z, rfl⟩ := Finset.card_eq_one.mp h1
    have hz := hT.1 (Finset.mem_singleton_self z)
    obtain ⟨x, hx, hd⟩ := h z hz
    obtain ⟨w, hw, hlt⟩ := hT.2 x hx
    rw [Finset.mem_singleton.mp hw] at hlt
    exact (not_lt_of_ge hd) hlt
  exact_mod_cast hcard

theorem push_net
    (h : ∀ x ∈ U, ∀ y ∈ U, eIn x y < r → eOut (f.func x) (f.func y) < eps)
    {S : Finset X} (hS : InternalEpsilonNet eIn r U S) :
    ∃ T : Finset X, (↑T : Set X) = f.func '' (↑S : Set X) ∧
      InternalEpsilonNet eOut eps (f.func '' U) T ∧ T.card ≤ S.card := by
  classical
  refine ⟨S.image f.func, Finset.coe_image, ⟨?_, ?_⟩, Finset.card_image_le⟩
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hy
    exact image_mem f (hS.1 hs)
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hab⟩ := hS.2 x hx
    exact ⟨f.func s, Finset.mem_image_of_mem _ hs, h x hx s (hS.1 hs) hab⟩

theorem pull_net
    (h : ∀ x ∈ U, ∀ y ∈ U, eOut (f.func x) (f.func y) < eps → eIn x y < r)
    {T : Finset X} (hT : InternalEpsilonNet eOut eps (f.func '' U) T) :
    ∃ S : Finset X, f.func '' (↑S : Set X) = (↑T : Set X) ∧
      InternalEpsilonNet eIn r U S ∧ S.card ≤ T.card := by
  classical
  let pick (t : (T : Set X)) : X := (hT.1 t.2).choose
  have hp (t : (T : Set X)) : pick t ∈ U ∧ f.func (pick t) = t :=
    (hT.1 t.2).choose_spec
  let S := T.attach.image pick
  refine ⟨S, ?_, ⟨?_, ?_⟩, Finset.card_image_le.trans (by simp)⟩
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
      exact (hp t).2 ▸ t.2
    · intro hy
      exact ⟨pick ⟨y, hy⟩, Finset.mem_image_of_mem _ (Finset.mem_attach _ _), (hp ⟨y, hy⟩).2⟩
  · intro x hx
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hp t).1
  · intro x hx
    obtain ⟨t, ht, hxt⟩ := hT.2 (f.func x) (image_mem f hx)
    let z : (T : Set X) := ⟨t, ht⟩
    exact ⟨pick z, Finset.mem_image_of_mem _ (Finset.mem_attach _ _),
      h x hx _ (hp z).1 (by rwa [(hp z).2])⟩

theorem image_cover_le
    (h : ∀ x ∈ U, ∀ y ∈ U, eIn x y < r → eOut (f.func x) (f.func y) < eps) :
    covering_number eOut eps (f.func '' U) ≤ covering_number eIn r U := by
  apply le_cover_of_le_cards
  intro S hS
  obtain ⟨T, _, hT, hcard⟩ := push_net h hS
  exact (cover_le_card hT).trans (Nat.cast_le.mpr hcard)

theorem cover_le_image
    (h : ∀ x ∈ U, ∀ y ∈ U, eOut (f.func x) (f.func y) < eps → eIn x y < r) :
    covering_number eIn r U ≤ covering_number eOut eps (f.func '' U) := by
  apply le_cover_of_le_cards
  intro T hT
  obtain ⟨S, _, hS, hcard⟩ := pull_net h hT
  exact (cover_le_card hS).trans (Nat.cast_le.mpr hcard)

theorem threshold_cover (hA : A.Nonempty) (hdom : A ⊆ dom f) (i j : I)
    {tn : ENNReal} (htn : FiniteRadius tn) (h : tn ≤ nullMatrix d f A j i)
    (hB : B ⊆ A) (heps : FiniteRadius eps) :
    covering_number (d j) eps (f.func '' B) ≤ covering_number (d i) tn B := by
  apply image_cover_le
  intro x hx y hy hxy
  have hmem := threshold_fiber hA hdom i j htn h (hB hy)
    (show x ∈ ball (d i) y tn ∩ A from ⟨hxy, hB hx⟩)
  exact hmem.2.trans_lt heps.1

theorem threshold_entropy (hA : A.Nonempty) (hdom : A ⊆ dom f) (i j : I)
    {tn : ENNReal} (htn : FiniteRadius tn) (h : tn ≤ nullMatrix d f A j i)
    (_hBne : B.Nonempty) (hB : B ⊆ A) (heps : FiniteRadius eps) :
    metric_entropy (d j) eps (f.func '' B) ≤ metric_entropy (d i) tn B :=
  log2_mono (threshold_cover hA hdom i j htn h hB heps)

theorem const_image_cover (hU : U.Nonempty) (heps : FiniteRadius eps)
    (h : ∀ x ∈ U, ∀ y ∈ U, e (f.func x) (f.func y) = 0) :
    covering_number e eps (f.func '' U) = 1 := by
  apply cover_one_of_close (hU.image f.func)
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (h x hx y hy).trans_lt heps.1

theorem small_domain_cover (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (hA : A.Nonempty)
    (hdom : A ⊆ dom f) (i j : I) {ts tn : ENNReal} (hts : FiniteRadius ts) (htn : FiniteRadius tn)
    (hsmall : diameter (d i) A < ts) (hst : ts ≤ tn) (hn : tn ≤ nullMatrix d f A j i)
    (heps : FiniteRadius eps) : covering_number (d j) eps (f.func '' A) = 1 :=
  const_image_cover hA heps ((small_domain_iff hd hA hdom i j hts htn hsmall hst).mp hn)

def EntropyAdmissible (eIn eOut : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (eps : ENNReal) : Prop :=
  covering_number eIn eps U < ⊤ ∨ covering_number eOut eps (f.func '' U) < ⊤

noncomputable def entropyDifference (eIn eOut : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (eps : ENNReal) (_hU : U.Nonempty) (_hdom : U ⊆ dom f)
    (_heps : FiniteRadius eps) (_h : EntropyAdmissible eIn eOut f U eps) : EReal :=
  metric_entropy eIn eps U - metric_entropy eOut eps (f.func '' U)

noncomputable def mappingEntropyDifference (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (eps : ENNReal) (Jin Jout : Set I) (_hin : Jin.Nonempty) (_hout : Jout.Nonempty)
    (hU : U.Nonempty) (hdom : U ⊆ dom f) (heps : FiniteRadius eps)
    (h : EntropyAdmissible (subfamily_pseudometric d Jin) (subfamily_pseudometric d Jout) f U eps) :
    EReal :=
  entropyDifference _ _ f U eps hU hdom heps h

theorem mappingEntropyDifference_eq_sub
    {Jin Jout : Set I} (hin : Jin.Nonempty) (hout : Jout.Nonempty)
    (hU : U.Nonempty) (hdom : U ⊆ dom f) (heps : FiniteRadius eps)
    (h : subfamilyCover d Jin eps U < ⊤ ∨ subfamilyCover d Jout eps (f.func '' U) < ⊤) :
    mappingEntropyDifference d f U eps Jin Jout hin hout hU hdom heps h =
      subfamily_metric_entropy d Jin eps U - subfamily_metric_entropy d Jout eps (f.func '' U) :=
  rfl

theorem mappingEntropyDifference_singletons (i j : I)
    (hU : U.Nonempty) (hdom : U ⊆ dom f) (heps : FiniteRadius eps)
    (h : EntropyAdmissible (d i) (d j) f U eps) :
    let h' : EntropyAdmissible (subfamily_pseudometric d {i}) (subfamily_pseudometric d {j}) f U eps :=
      by simpa only [subfamily_pseudometric_singleton] using h
    mappingEntropyDifference d f U eps {i} {j} (Set.singleton_nonempty i) (Set.singleton_nonempty j)
      hU hdom heps h' = entropyDifference (d i) (d j) f U eps hU hdom heps h := by
  simp only [mappingEntropyDifference, entropyDifference, subfamily_pseudometric_singleton]

theorem entropy_admissible_iff (hU : U.Nonempty) :
    EntropyAdmissible eIn eOut f U eps ↔
      metric_entropy eIn eps U ≠ ⊤ ∨ metric_entropy eOut eps (f.func '' U) ≠ ⊤ := by
  rw [entropy_ne_top_iff hU, entropy_ne_top_iff (hU.image f.func)]
  rfl

theorem entropy_difference_finite (hU : U.Nonempty) (hdom : U ⊆ dom f) (heps : FiniteRadius eps)
    (hi : covering_number eIn eps U < ⊤) (ho : covering_number eOut eps (f.func '' U) < ⊤) :
    entropyDifference eIn eOut f U eps hU hdom heps (Or.inl hi) =
      ((Real.logb 2 (covering_number eIn eps U).toReal -
        Real.logb 2 (covering_number eOut eps (f.func '' U)).toReal : ℝ) : EReal) := by
  rw [entropyDifference, entropy_coe hU hi, entropy_coe (hU.image f.func) ho, EReal.coe_sub]

theorem entropy_difference_input_top (hU : U.Nonempty) (hdom : U ⊆ dom f) (heps : FiniteRadius eps)
    (hi : covering_number eIn eps U = ⊤) (ho : covering_number eOut eps (f.func '' U) < ⊤) :
    entropyDifference eIn eOut f U eps hU hdom heps (Or.inr ho) = ⊤ := by
  rw [entropyDifference, entropy_top hi, entropy_coe (hU.image f.func) ho, EReal.top_sub_coe]

theorem entropy_difference_output_top (hU : U.Nonempty) (hdom : U ⊆ dom f) (heps : FiniteRadius eps)
    (hi : covering_number eIn eps U < ⊤) (ho : covering_number eOut eps (f.func '' U) = ⊤) :
    entropyDifference eIn eOut f U eps hU hdom heps (Or.inl hi) = ⊥ := by
  rw [entropyDifference, entropy_top ho, EReal.sub_top]

theorem entropy_difference_sign (hU : U.Nonempty) (hdom : U ⊆ dom f) (heps : FiniteRadius eps)
    (h : EntropyAdmissible eIn eOut f U eps) :
    let a := metric_entropy eIn eps U
    let b := metric_entropy eOut eps (f.func '' U)
    let diff := entropyDifference eIn eOut f U eps hU hdom heps h
    (0 < diff ↔ b < a) ∧ (diff < 0 ↔ a < b) ∧ (diff = 0 ↔ a = b) := by
  have ht := (entropy_admissible_iff hU).mp h
  have hb : metric_entropy eIn eps U ≠ ⊥ ∨ metric_entropy eOut eps (f.func '' U) ≠ ⊥ :=
    Or.inl (entropy_ne_bot hU)
  dsimp [entropyDifference]
  refine ⟨EReal.sub_pos, EReal.sub_neg ht hb, ?_⟩
  rw [le_antisymm_iff, le_antisymm_iff, EReal.sub_nonpos, EReal.sub_nonneg ht hb]

theorem finite_domain_entropy (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (hU : U.Nonempty)
    (hdom : U ⊆ dom f) (hfin : U.Finite) (heps : FiniteRadius eps) {Jin Jout : Set I}
    (hin : Jin.Nonempty) (hout : Jout.Nonempty) :
    let a := subfamilyCover d Jin eps U
    let b := subfamilyCover d Jout eps (f.func '' U)
    (0 < a ∧ a < ⊤) ∧ (0 < b ∧ b < ⊤) ∧
      ∃ (h : EntropyAdmissible (subfamily_pseudometric d Jin) (subfamily_pseudometric d Jout) f U eps)
        (s t : ℝ),
        subfamily_metric_entropy d Jin eps U = s ∧
          subfamily_metric_entropy d Jout eps (f.func '' U) = t ∧
          mappingEntropyDifference d f U eps Jin Jout hin hout hU hdom heps h = ((s - t : ℝ) : EReal) := by
  let ei := subfamily_pseudometric_is_extended d Jin hin hd
  let eo := subfamily_pseudometric_is_extended d Jout hout hd
  have hi := finite_hasFiniteCovers ei.dist_self hfin eps heps
  have ho := finite_hasFiniteCovers eo.dist_self (hfin.image f.func) eps heps
  exact ⟨⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ hU), hi⟩,
    ⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ (hU.image f.func)), ho⟩,
    Or.inl hi, _, _, entropy_coe hU hi, entropy_coe (hU.image f.func) ho,
    entropy_difference_finite hU hdom heps hi ho⟩

theorem const_entropy (hU : U.Nonempty) (hdom : U ⊆ dom f) (heps : FiniteRadius eps)
    (j : I) (hj : j ∈ constPart d f U) :
    covering_number (d j) eps (f.func '' U) = 1 ∧ metric_entropy (d j) eps (f.func '' U) = 0 ∧
      ∃ h : EntropyAdmissible (d j) (d j) f U eps,
        entropyDifference (d j) (d j) f U eps hU hdom heps h = metric_entropy (d j) eps U := by
  have hn := const_image_cover hU heps hj
  have he : metric_entropy (d j) eps (f.func '' U) = 0 := by
    simp [metric_entropy, hn, log2_ereal]
  refine ⟨hn, he, Or.inr (by simp [hn]), ?_⟩
  simp [entropyDifference, he]

theorem id_cover_entropy (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (_hU : U.Nonempty)
    (hdom : U ⊆ dom f) (_heps : FiniteRadius eps) (j : I) (hj : j ∈ idPart d f U) :
    covering_number (d j) eps (f.func '' U) = covering_number (d j) eps U ∧
      metric_entropy (d j) eps (f.func '' U) = metric_entropy (d j) eps U := by
  have he := id_isometry hd hdom hj
  have hn : covering_number (d j) eps (f.func '' U) = covering_number (d j) eps U :=
    le_antisymm (image_cover_le fun x hx y hy => by simp only [he x hx y hy, imp_self])
      (cover_le_image fun x hx y hy => by simp only [he x hx y hy, imp_self])
  exact ⟨hn, congrArg log2_ereal hn⟩

theorem id_entropy_difference (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (hU : U.Nonempty)
    (hdom : U ⊆ dom f) (heps : FiniteRadius eps) (j : I) (hj : j ∈ idPart d f U)
    (h : EntropyAdmissible (d j) (d j) f U eps) :
    entropyDifference (d j) (d j) f U eps hU hdom heps h = 0 := by
  obtain ⟨hn, he⟩ := id_cover_entropy hd hU hdom heps j hj
  have hf : covering_number (d j) eps U < ⊤ := by
    rcases h with h | h
    · exact h
    · rwa [hn] at h
  rw [entropyDifference, he]
  exact EReal.sub_self ((entropy_ne_top_iff hU).mpr hf) (entropy_ne_bot hU)

theorem finiteRadius_div (hr : FiniteRadius r) (hL : FiniteRadius eps) : FiniteRadius (r / eps) :=
  ⟨ENNReal.div_pos (ne_of_gt hr.1) hL.2.ne, ENNReal.div_lt_top hr.2.ne (ne_of_gt hL.1)⟩

theorem lip_cover (_hU : U.Nonempty) (i j : I) {L : ENNReal}
    (hL : FiniteRadius L) (_heps : FiniteRadius eps) (h : HasScalarLipBound d f U i j L) :
    covering_number (d j) eps (f.func '' U) ≤ covering_number (d i) (eps / L) U :=
  image_cover_le fun x hx y hy hxy => (h.2 x hx y hy).trans_lt ((lt_div_iff hL).mp hxy)

theorem lip_entropy_difference (hU : U.Nonempty) (i j : I) {L : ENNReal}
    (hL : FiniteRadius L) (heps : FiniteRadius eps) (h : HasScalarLipBound d f U i j L)
    (ht : HasFiniteCovers (d i) U) :
    covering_number (d i) eps U < ⊤ ∧ covering_number (d j) eps (f.func '' U) < ⊤ ∧
      (∃ a b c : ℝ, metric_entropy (d i) eps U = a ∧
        metric_entropy (d j) eps (f.func '' U) = b ∧ metric_entropy (d i) (eps / L) U = c) ∧
      ∃ hfin : EntropyAdmissible (d i) (d j) f U eps,
        metric_entropy (d i) eps U - metric_entropy (d i) (eps / L) U ≤
          entropyDifference (d i) (d j) f U eps hU h.1 heps hfin := by
  have hn := lip_cover hU i j hL heps h
  have hf := ht _ (finiteRadius_div heps hL)
  have hi := ht _ heps
  have ho := hn.trans_lt hf
  exact ⟨hi, ho, ⟨_, _, _, entropy_coe hU hi, entropy_coe (hU.image _) ho, entropy_coe hU hf⟩,
    Or.inl hi, EReal.sub_le_sub le_rfl (log2_mono hn)⟩

theorem colip_cover [Fintype I] {K : I → I → ENNReal} (h : IsCoLipMatrix d f U K)
    (i j : I) (hK : FiniteRadius (K i j)) (_heps : FiniteRadius eps) :
    covering_number (d i) (eps / K i j) U ≤ covering_number (d j) eps (f.func '' U) := by
  apply cover_le_image
  intro x hx y hy hxy
  apply (lt_div_iff hK).mpr
  have hterm : K i j * d i x y ≤ ∑ k : I, K k j * d k x y :=
    Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)
  exact hterm.trans_lt ((h.2.2 x hx y hy j).trans_lt hxy)

theorem colip_entropy_difference [Fintype I] {K : I → I → ENNReal} (h : IsCoLipMatrix d f U K)
    (i j : I) (hK : FiniteRadius (K i j)) (heps : FiniteRadius eps) (ht : HasFiniteCovers (d i) U) :
    covering_number (d i) (eps / K i j) U < ⊤ ∧
      ∃ hfin : EntropyAdmissible (d i) (d j) f U eps,
        entropyDifference (d i) (d j) f U eps h.1 h.2.1 heps hfin ≤
          metric_entropy (d i) eps U - metric_entropy (d i) (eps / K i j) U :=
  ⟨ht _ (finiteRadius_div heps hK), Or.inl (ht _ heps),
    EReal.sub_le_sub le_rfl (log2_mono (colip_cover h i j hK heps))⟩

end MG03
