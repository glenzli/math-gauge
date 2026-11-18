import MG03.Core

namespace MG03

open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X} {d : I → X → X → ENNReal}
variable {eIn eOut : X → X → ENNReal} {f g : Operator X bot} {A B U : Set X}

def LegalRadius (eIn eOut : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) (r : ENNReal) : Prop :=
  FiniteRadius r ∧ ball eIn y r ∩ U ⊆ fiberAt eOut f U (f.func y)

noncomputable def radius (eIn eOut : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) : ENNReal :=
  sSup {r | LegalRadius eIn eOut f U y r}

theorem radius_singleton (i j : I) (y : X) :
    radius (d i) (subfamily_pseudometric d {j}) f U y = radius (d i) (d j) f U y := by
  rw [subfamily_pseudometric_singleton]

theorem legalRadius_iff {y : X} {r : ENNReal} :
    LegalRadius eIn eOut f U y r ↔
      FiniteRadius r ∧ ∀ x ∈ U, eIn x y < r → eOut (f.func x) (f.func y) = 0 :=
  ⟨fun h => ⟨h.1, fun x hx hd => (h.2 (show x ∈ ball eIn y r ∩ U from ⟨hd, hx⟩)).2⟩,
    fun h => ⟨h.1, fun x hx => ⟨hx.2, h.2 x hx.2 hx.1⟩⟩⟩

theorem radius_ge_legal {y : X} {r : ENNReal} (h : LegalRadius eIn eOut f U y r) :
    r ≤ radius eIn eOut f U y :=
  le_sSup h

theorem exists_legal_above {y : X} {a : ENNReal} (h : a < radius eIn eOut f U y) :
    ∃ r, LegalRadius eIn eOut f U y r ∧ a < r :=
  lt_sSup_iff.mp h

theorem radius_eq_zero_of_no_legal {y : X} (h : ¬ ∃ r, LegalRadius eIn eOut f U y r) :
    radius eIn eOut f U y = 0 :=
  le_antisymm (sSup_le fun r hr => (h ⟨r, hr⟩).elim) (zero_le _)

theorem radius_eq_top_of_all_legal {y : X} (h : ∀ r, FiniteRadius r → LegalRadius eIn eOut f U y r) :
    radius eIn eOut f U y = ⊤ := by
  refine top_unique (le_of_forall_lt fun a ha => ?_)
  obtain ⟨r, har, hr⟩ := exists_between ha
  exact har.trans_le (radius_ge_legal (h r ⟨(zero_le a).trans_lt har, hr⟩))

theorem le_radius_iff {y : X} {a : ENNReal} :
    a ≤ radius eIn eOut f U y ↔ ∀ x ∈ U, eIn x y < a → eOut (f.func x) (f.func y) = 0 := by
  constructor
  · intro h x hx hdist
    obtain ⟨r, hr, hlt⟩ := exists_legal_above (hdist.trans_le h)
    exact (legalRadius_iff.mp hr).2 x hx hlt
  · intro h
    apply le_of_forall_lt
    intro b hb
    obtain ⟨r, hbr, hra⟩ := exists_between hb
    refine hbr.trans_le (radius_ge_legal (legalRadius_iff.mpr ⟨⟨?_, ?_⟩, ?_⟩))
    · exact (zero_le b).trans_lt hbr
    · exact hra.trans_le le_top
    · exact fun x hx hx' => h x hx (hx'.trans hra)

theorem radius_eq_iInf {y : X} :
    radius eIn eOut f U y =
      ⨅ x : {x ∈ U | eOut (f.func x) (f.func y) ≠ 0}, eIn x.1 y := by
  apply le_antisymm
  · exact le_iInf fun x => le_of_not_gt fun hx =>
      x.2.2 (le_radius_iff.mp le_rfl x.1 x.2.1 hx)
  · apply le_radius_iff.mpr
    intro x hx hdist
    by_contra hz
    exact (not_lt_of_ge (iInf_le
      (fun z : {z ∈ U | eOut (f.func z) (f.func y) ≠ 0} => eIn z.1 y) ⟨x, hx, hz⟩)) hdist

noncomputable def uniformRadius (eIn eOut : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) : ENNReal := ⨅ y : A, radius eIn eOut f U y

noncomputable def uniformOn (eIn eOut : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) : ENNReal := uniformRadius eIn eOut f U U

/-- Ordinary matrix indexing: output row, then input column. -/
noncomputable def nullMatrix (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) : I → I → ENNReal :=
  fun j i => uniformOn (d i) (d j) f U

theorem uniform_le_point {y : X} (hy : y ∈ A) :
    uniformRadius eIn eOut f A U ≤ radius eIn eOut f U y :=
  iInf_le (fun z : A => radius eIn eOut f U z.1) ⟨y, hy⟩

theorem le_uniform_iff {a : ENNReal} :
    a ≤ uniformRadius eIn eOut f A U ↔
      ∀ y ∈ A, ∀ x ∈ U, eIn x y < a → eOut (f.func x) (f.func y) = 0 := by
  constructor
  · intro h y hy
    exact le_radius_iff.mp (h.trans (uniform_le_point hy))
  · intro h
    exact le_iInf fun y : A => le_radius_iff.mpr (h y.1 y.2)

theorem uniform_eq_top_of_const
    (h : ∀ x ∈ U, ∀ y ∈ U, eOut (f.func x) (f.func y) = 0) :
    uniformOn eIn eOut f U = ⊤ :=
  top_unique (le_uniform_iff.mpr fun y hy x hx _ => h x hx y hy)

theorem uniform_le_of_separated {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h : eOut (f.func x) (f.func y) ≠ 0) :
    uniformOn eIn eOut f U ≤ eIn x y :=
  le_of_not_gt fun hlt => h (le_uniform_iff.mp le_rfl y hy x hx hlt)

theorem const_subfamily_fiber (_hUne : U.Nonempty) (_hU : U ⊆ dom f)
    {J : Set I} (_hJ : J.Nonempty) (h : J ⊆ constPart d f U) {y : X} (hy : y ∈ U) :
    fiber d J f U (f.func y) = U :=
  Subset.antisymm (fun _ hx => hx.1)
    (fun x hx => ⟨hx, subfamily_zero_iff.mpr fun _ hj => h hj x hx y hy⟩)

theorem const_subfamily_radii (hUne : U.Nonempty) (hU : U ⊆ dom f)
    {J : Set I} (hJ : J.Nonempty) (h : J ⊆ constPart d f U) (i : I) :
    (∀ y ∈ U, radius (d i) (subfamily_pseudometric d J) f U y = ⊤) ∧
      uniformOn (d i) (subfamily_pseudometric d J) f U = ⊤ := by
  have hpoint : ∀ y ∈ U, radius (d i) (subfamily_pseudometric d J) f U y = ⊤ := by
    intro y hy
    apply top_unique (le_radius_iff.mpr ?_)
    intro x hx _
    have hmem : x ∈ fiber d J f U (f.func y) := by
      rwa [const_subfamily_fiber hUne hU hJ h hy]
    exact hmem.2
  exact ⟨hpoint, top_unique (le_iInf fun y : U => le_of_eq (hpoint y y.2).symm)⟩

theorem id_image_fiber (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f) {i : I} (hi : i ∈ idPart d f U) {y : X} (hy : y ∈ U) :
    fiberAt (d i) f U (f.func y) = {x ∈ U | d i x y = 0} :=
  Set.ext fun x => and_congr_right fun hx => by rw [id_isometry hd hU hi x hx y hy]

theorem id_radius_lower (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f) {i : I} (hi : i ∈ idPart d f U) {y : X} (hy : y ∈ U)
    {r : ENNReal} (hr : FiniteRadius r)
    (h : ball (d i) y r ∩ U ⊆ {x ∈ U | d i x y = 0}) :
    r ≤ radius (d i) (d i) f U y ∧ 0 < r :=
  ⟨radius_ge_legal ⟨hr, by rwa [id_image_fiber hd hU hi hy]⟩, hr.1⟩

theorem radius_subfamily_iInf (_hU : U ⊆ dom f) {y : X} (_hy : y ∈ U)
    (i : I) (J : Set I) :
    radius (d i) (subfamily_pseudometric d J) f U y =
      ⨅ j : J, radius (d i) (d j.1) f U y := by
  apply le_antisymm
  · refine le_iInf fun j => le_radius_iff.mpr fun x hx hdist => ?_
    exact subfamily_zero_iff.mp (le_radius_iff.mp le_rfl x hx hdist) j j.2
  · refine le_radius_iff.mpr fun x hx hdist => subfamily_zero_iff.mpr fun j hj => ?_
    have hle := iInf_le (fun k : J => radius (d i) (d k.1) f U y) ⟨j, hj⟩
    exact le_radius_iff.mp hle x hx hdist

theorem finite_iInf_min {T : Type} [Finite T] [Nonempty T] (a : T → ENNReal) :
    ∃ t, (⨅ s, a s) = a t ∧ ∀ s, a t ≤ a s := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  obtain ⟨t, _, ht⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  have h : ∀ s, a t ≤ a s := fun s => ht s (Finset.mem_univ s)
  exact ⟨t, le_antisymm (iInf_le _ t) (le_iInf h), h⟩

theorem radius_subfamily_min [Finite I] (hU : U ⊆ dom f) {y : X} (hy : y ∈ U)
    (i : I) {J : Set I} (hJ : J.Nonempty) :
    ∃ j : J, radius (d i) (subfamily_pseudometric d J) f U y = radius (d i) (d j.1) f U y ∧
      ∀ k : J, radius (d i) (d j.1) f U y ≤ radius (d i) (d k.1) f U y := by
  letI : Nonempty J := hJ.to_subtype
  rw [radius_subfamily_iInf hU hy]
  exact finite_iInf_min _

theorem uniform_subfamily_iInf (_hUne : U.Nonempty) (hU : U ⊆ dom f) (i : I) (J : Set I) :
    uniformOn (d i) (subfamily_pseudometric d J) f U = ⨅ j : J, nullMatrix d f U j.1 i := by
  change (⨅ y : U, radius (d i) (subfamily_pseudometric d J) f U y) =
    ⨅ j : J, ⨅ y : U, radius (d i) (d j.1) f U y
  simp_rw [radius_subfamily_iInf hU (Subtype.property _)]
  exact iInf_comm

theorem uniform_subfamily_min [Finite I] (hUne : U.Nonempty) (hU : U ⊆ dom f)
    (i : I) {J : Set I} (hJ : J.Nonempty) :
    ∃ j : J, uniformOn (d i) (subfamily_pseudometric d J) f U = nullMatrix d f U j.1 i ∧
      ∀ k : J, nullMatrix d f U j.1 i ≤ nullMatrix d f U k.1 i := by
  letI : Nonempty J := hJ.to_subtype
  rw [uniform_subfamily_iInf hUne hU]
  exact finite_iInf_min _

theorem uniform_subfamily_antitone (hUne : U.Nonempty) (hU : U ⊆ dom f) (i : I)
    {J K : Set I} (_hJ : J.Nonempty) (_hK : K.Nonempty) (hJK : J ⊆ K) :
    uniformOn (d i) (subfamily_pseudometric d K) f U ≤
      uniformOn (d i) (subfamily_pseudometric d J) f U := by
  rw [uniform_subfamily_iInf hUne hU, uniform_subfamily_iInf hUne hU]
  exact le_iInf fun j : J => iInf_le _ (⟨j.1, hJK j.2⟩ : K)

theorem fiber_truncation (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom f) (j : I) {y z : X} (_hy : y ∈ U) (_hz : z ∈ U)
    (h : z ∈ fiberAt (d j) f U (f.func y)) :
    d j (f.func y) (f.func z) = 0 :=
  ((hd j).symm _ _).trans h.2

theorem radius_truncation (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f) (i j : I) {y z : X} (hy : y ∈ U) (hz : z ∈ U)
    (h : d i y z < radius (d i) (d j) f U y) :
    d j (f.func y) (f.func z) = 0 := by
  obtain ⟨r, hr, hlt⟩ := exists_legal_above h
  exact fiber_truncation hd hU j hy hz
    (hr.2 ⟨show d i z y < r by rwa [(hd i).symm z y], hz⟩)

theorem comp_fiber_truncation (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom g) (j : I) {x x' : X} (_hx : x ∈ dom f) (_hx' : x' ∈ dom f)
    (hy : f.func x ∈ U) (hy' : f.func x' ∈ U)
    (h : f.func x' ∈ fiberAt (d j) g U (g.func (f.func x))) :
    d j ((g * f).func x) ((g * f).func x') = 0 :=
  fiber_truncation hd hU j hy hy' h

theorem comp_null_propagation (_hUne : U.Nonempty) (_hU : U ⊆ dom (g * f)) (i j l : I)
    (h : ∀ y ∈ f.func '' U, ∀ z ∈ f.func '' U, d l y z = 0 → d j (g.func y) (g.func z) = 0) :
    nullMatrix d f U l i ≤ nullMatrix d (g * f) U j i := by
  refine le_uniform_iff.mpr fun y hy x hx hdist => h _ (image_mem f hx) _ (image_mem f hy) ?_
  exact le_uniform_iff.mp le_rfl y hy x hx hdist

theorem lt_div_iff {a b L : ENNReal} (hL : FiniteRadius L) :
    a < b / L ↔ L * a < b := by
  rw [mul_comm]
  exact ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hL.1)) (Or.inl hL.2.ne)

theorem comp_null_pullback (_hUne : U.Nonempty) (_hU : U ⊆ dom (g * f))
    (i j l : I) {L : ENNReal} (hL : FiniteRadius L)
    (h : ∀ x ∈ U, ∀ y ∈ U, d l (f.func x) (f.func y) ≤ L * d i x y) :
    nullMatrix d g (f.func '' U) j l / L ≤ nullMatrix d (g * f) U j i := by
  refine le_uniform_iff.mpr fun y hy x hx hdist => ?_
  exact le_uniform_iff.mp le_rfl _ (image_mem f hy) _ (image_mem f hx)
    ((h x hx y hy).trans_lt ((lt_div_iff hL).mp hdist))

structure InputScale (X I : Type) where
  value : I → {A : Set X // A.Nonempty} → ENNReal
  mono : ∀ i A B, A.1 ⊆ B.1 → value i A ≤ value i B

noncomputable def diameter (e : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x : A, ⨆ y : A, e x.1 y.1

theorem le_diameter {e : X → X → ENNReal} {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    e x y ≤ diameter e A :=
  le_iSup_of_le (⟨x, hx⟩ : A) (le_iSup (fun z : A => e x z.1) ⟨y, hy⟩)

theorem diameter_le {e : X → X → ENNReal} {r : ENNReal}
    (h : ∀ x ∈ A, ∀ y ∈ A, e x y ≤ r) : diameter e A ≤ r :=
  iSup_le fun x : A => iSup_le fun y : A => h x x.2 y y.2

noncomputable def diameterScale (d : I → X → X → ENNReal) : InputScale X I :=
  ⟨fun i A => diameter (d i) A.1, fun i _ _ h =>
    diameter_le fun _ hx _ hy => le_diameter (e := d i) (h hx) (h hy)⟩

noncomputable def channelType (s : InputScale X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : {A : Set X // A.Nonempty}) (ts tn : ENNReal) (i j : I) :
    Bool × Bool :=
  (decide (s.value i A < ts), decide (tn ≤ nullMatrix d f A.1 j i))

theorem channel_cases (s : InputScale X I) (hA : A.Nonempty) (_hdom : A ⊆ dom f)
    {ts tn : ENNReal} (_hs : FiniteRadius ts) (_hn : FiniteRadius tn) (i j : I) :
    let c := channelType s d f ⟨A, hA⟩ ts tn i j
    let S := s.value i ⟨A, hA⟩
    let N := nullMatrix d f A j i
    (c = (true, true) ↔ S < ts ∧ tn ≤ N) ∧
    (c = (true, false) ↔ S < ts ∧ N < tn) ∧
    (c = (false, true) ↔ ts ≤ S ∧ tn ≤ N) ∧
    (c = (false, false) ↔ ts ≤ S ∧ N < tn) := by
  simp [channelType, not_lt, not_le]

theorem channel_exhaustive (c : Bool × Bool) :
    c = (true, true) ∨ c = (true, false) ∨ c = (false, true) ∨ c = (false, false) := by
  obtain ⟨a, b⟩ := c
  cases a <;> cases b <;> simp

theorem channel_cases_distinct :
    ([(true, true), (true, false), (false, true), (false, false)] : List (Bool × Bool)).Nodup := by
  decide

theorem channel_scale_mono (s : InputScale X I) (hA : A.Nonempty) (_hdom : A ⊆ dom f)
    {ts ts' tn : ENNReal} (_hs : FiniteRadius ts) (_hs' : FiniteRadius ts')
    (_hn : FiniteRadius tn) (h : ts ≤ ts') :
    {p : I × I | (channelType s d f ⟨A, hA⟩ ts tn p.1 p.2).1 = true} ⊆
      {p : I × I | (channelType s d f ⟨A, hA⟩ ts' tn p.1 p.2).1 = true} := by
  intro p hp
  simp only [Set.mem_setOf_eq, channelType, decide_eq_true_eq] at *
  exact hp.trans_le h

theorem channel_null_antitone (s : InputScale X I) (hA : A.Nonempty) (_hdom : A ⊆ dom f)
    {ts tn tn' : ENNReal} (_hs : FiniteRadius ts) (_hn : FiniteRadius tn)
    (_hn' : FiniteRadius tn') (h : tn ≤ tn') :
    {p : I × I | (channelType s d f ⟨A, hA⟩ ts tn' p.1 p.2).2 = true} ⊆
      {p : I × I | (channelType s d f ⟨A, hA⟩ ts tn p.1 p.2).2 = true} := by
  intro p hp
  simp only [Set.mem_setOf_eq, channelType, decide_eq_true_eq] at *
  exact h.trans hp

theorem scale_restrict (s : InputScale X I) (hA : A.Nonempty) (hB : B.Nonempty)
    (_hdom : A ⊆ dom f) (hBA : B ⊆ A) (i : I) {ts : ENNReal} (_hts : FiniteRadius ts) :
    s.value i ⟨B, hB⟩ ≤ s.value i ⟨A, hA⟩ ∧
      (s.value i ⟨A, hA⟩ < ts → s.value i ⟨B, hB⟩ < ts) :=
  ⟨s.mono i _ _ hBA, (s.mono i _ _ hBA).trans_lt⟩

theorem radius_restrict (_hdom : A ⊆ dom f) (hBA : B ⊆ A) {y : X} (_hy : y ∈ B) :
    radius eIn eOut f A y ≤ radius eIn eOut f B y :=
  le_radius_iff.mpr fun x hx => le_radius_iff.mp le_rfl x (hBA hx)

theorem uniform_restrict (_hB : B.Nonempty) (hdom : A ⊆ dom f) (hBA : B ⊆ A) :
    uniformOn eIn eOut f A ≤ uniformOn eIn eOut f B :=
  le_iInf fun y : B => (uniform_le_point (hBA y.2)).trans (radius_restrict hdom hBA y.2)

theorem below_uniform (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hA : A.Nonempty) (hdom : A ⊆ dom f) (i j : I)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A) (h : d i x y < nullMatrix d f A j i) :
    d j (f.func x) (f.func y) = 0 :=
  radius_truncation hd hdom i j hx hy (h.trans_le (uniform_le_point hx))

theorem separated_above_uniform (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hA : A.Nonempty) (hdom : A ⊆ dom f) (i j : I)
    {x y : X} (hx : x ∈ A) (hy : y ∈ A) (h : 0 < d j (f.func x) (f.func y)) :
    nullMatrix d f A j i ≤ d i x y :=
  le_of_not_gt fun hlt => (ne_of_gt h) (below_uniform hd hA hdom i j hx hy hlt)

theorem uniform_separation_witness (_hA : A.Nonempty) (_hdom : A ⊆ dom f) (i j : I)
    {tn a : ENNReal} (_htn : FiniteRadius tn) (_hlt : nullMatrix d f A j i < tn)
    (_ha : FiniteRadius a) (h₁ : nullMatrix d f A j i < a) (_h₂ : a < tn) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ eps, FiniteRadius eps ∧
      d i x y < a ∧ eps ≤ d j (f.func x) (f.func y) := by
  classical
  have h := mt le_uniform_iff.mpr (not_le.mpr h₁)
  push Not at h
  obtain ⟨y, hy, x, hx, hd, hz⟩ := h
  have hpos : 0 < d j (f.func x) (f.func y) := bot_lt_iff_ne_bot.mpr hz
  obtain ⟨eps, he, he'⟩ := exists_between hpos
  exact ⟨x, hx, y, hy, eps, ⟨he, he'.trans_le le_top⟩, hd, he'.le⟩

theorem threshold_fiber (_hA : A.Nonempty) (_hdom : A ⊆ dom f) (i j : I)
    {tn : ENNReal} (_htn : FiniteRadius tn) (h : tn ≤ nullMatrix d f A j i)
    {x : X} (hx : x ∈ A) :
    ball (d i) x tn ∩ A ⊆ fiberAt (d j) f A (f.func x) :=
  fun y hy => ⟨hy.2, le_uniform_iff.mp h x hx y hy.2 hy.1⟩

theorem small_domain_iff (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hA : A.Nonempty) (hdom : A ⊆ dom f) (i j : I) {ts tn : ENNReal}
    (_hts : FiniteRadius ts) (_htn : FiniteRadius tn) (hsmall : diameter (d i) A < ts)
    (hst : ts ≤ tn) :
    tn ≤ nullMatrix d f A j i ↔ ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0 := by
  constructor
  · intro h x hx y hy
    exact below_uniform hd hA hdom i j hx hy ((le_diameter hx hy).trans_lt
      (hsmall.trans_le (hst.trans h)))
  · intro h
    change tn ≤ uniformOn (d i) (d j) f A
    rw [uniform_eq_top_of_const h]
    exact le_top

theorem gap_at_point (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) [Fintype I]
    (_hUne : U.Nonempty) (hdom : U ⊆ dom f) {K : I → I → ENNReal} (hK : IsCoLipMatrix d f U K)
    (i j : I) (hk : 0 < K i j) {y : X} (hy : y ∈ U)
    (_hr : 0 < radius (d i) (d j) f U y) {x : X} (hx : x ∈ U) :
    d i x y ∉ Ioo 0 (radius (d i) (d j) f U y) := by
  intro h
  have hz := radius_truncation hd hdom i j hy hx (by simpa only [(hd i).symm y x] using h.2)
  have hz' := positive_colip_entry_reflects_zero d f U K i j hK hk
    x hx y hy (((hd j).symm _ _).trans hz)
  exact (ne_of_gt h.1) hz'

theorem gap_uniform (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) [Fintype I]
    (hUne : U.Nonempty) (hdom : U ⊆ dom f) {K : I → I → ENNReal} (hK : IsCoLipMatrix d f U K)
    (i j : I) (hk : 0 < K i j) (hr : 0 < nullMatrix d f U j i) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) :
    d i x y ∈ ({0} : Set ENNReal) ∪ Ici (nullMatrix d f U j i) := by
  by_cases h : d i x y = 0
  · exact Or.inl h
  · apply Or.inr
    exact le_of_not_gt fun hlt => gap_at_point hd hUne hdom hK i j hk hy
      (hr.trans_le (uniform_le_point hy)) hx
      ⟨bot_lt_iff_ne_bot.mpr h, hlt.trans_le (uniform_le_point hy)⟩

theorem gap_branches_disjoint {a : ENNReal} (ha : 0 < a) :
    Disjoint ({0} : Set ENNReal) (Ici a) := by
  simp [not_le.mpr ha]

end MG03
