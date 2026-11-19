import Chapter.Radius
import Mathlib.Data.EReal.Operations

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open scoped ENNReal
namespace Chapter

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {f : Operator X bot} {U A B : Set X} {i j : I}
variable {P Q : X → X → ℝ≥0∞} {r s : ℝ≥0∞}

theorem net_iff_ball_cover {S : Finset X} :
    InternalEpsilonNet P r U S ↔ ↑S ⊆ U ∧ U ⊆ ⋃ c ∈ S, ball P c r := by
  simp [InternalEpsilonNet, Set.subset_def, ball]

def TotallyBoundedAt (P : X → X → ℝ≥0∞) (U : Set X) : Prop :=
  ∀ r, FinitePositive r → covering_number P r U < ⊤

theorem total_iff_nets :
    TotallyBoundedAt P U ↔ ∀ r, FinitePositive r →
      ∃ S, InternalEpsilonNet P r U S := by
  classical
  unfold TotallyBoundedAt
  constructor <;> intro h r hr
  · by_contra hn
    exact (h r hr).ne ((covering_number_eq_top_iff P r U).mpr hn)
  · exact lt_top_iff_ne_top.mpr fun he => (covering_number_eq_top_iff P r U).mp he (h r hr)

theorem cover_le_card {S : Finset X} (h : InternalEpsilonNet P r U S) :
    covering_number P r U ≤ S.card :=
  iInf_le_of_le S (iInf_le_of_le h le_rfl)

theorem card_lower_cover {n : ℕ} (h : ∀ S, InternalEpsilonNet P r U S → n ≤ S.card) :
    (n : ℝ≥0∞) ≤ covering_number P r U :=
  le_iInf fun S => le_iInf fun hs => by exact_mod_cast h S hs

theorem cover_single_center (hy : ∃ y ∈ U, ∀ x ∈ U, P x y < r) :
    covering_number P r U = 1 := by
  classical
  obtain ⟨y,hy,h⟩ := hy
  have hn : InternalEpsilonNet P r U {y} := by
    refine ⟨by simpa, fun x hx => ⟨y,Finset.mem_singleton_self _, h x hx⟩⟩
  apply le_antisymm
  · simpa using cover_le_card hn
  · exact one_le_covering_number_of_nonempty _ _ _ ⟨y,hy⟩

theorem cover_finite (hU : U.Finite) (hP : ∀ x ∈ U, P x x = 0) (hr : 0 < r) :
    covering_number P r U < ⊤ := by
  classical
  have hn : InternalEpsilonNet P r U hU.toFinset := by
    refine ⟨by simp, fun x hx => ⟨x, hU.mem_toFinset.mpr hx, ?_⟩⟩
    rwa [hP x hx]
  exact (cover_le_card hn).trans_lt (ENNReal.natCast_lt_top _)

theorem cover_push (F : X → X)
    (h : ∀ x ∈ U, ∀ c ∈ U, P x c < r → Q (F x) (F c) < s) :
    covering_number Q s (F '' U) ≤ covering_number P r U := by
  classical
  refine le_iInf fun S => le_iInf fun hS => ?_
  have hn : InternalEpsilonNet Q s (F '' U) (S.image F) := by
    constructor
    · intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      exact ⟨x,hS.1 hx,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨c,hc,hxc⟩ := hS.2 x hx
      exact ⟨F c,Finset.mem_image_of_mem _ hc,h x hx c (hS.1 hc) hxc⟩
  exact (cover_le_card hn).trans (by exact_mod_cast Finset.card_image_le)

theorem cover_pull (F : X → X)
    (h : ∀ x ∈ U, ∀ c ∈ U, Q (F x) (F c) < s → P x c < r) :
    covering_number P r U ≤ covering_number Q s (F '' U) := by
  classical
  refine le_iInf fun T => le_iInf fun hT => ?_
  have pre (t : T) : ∃ x ∈ U, F x = (t : X) := hT.1 t.2
  let pick (t : T) := (pre t).choose
  have pick_mem (t : T) : pick t ∈ U := (pre t).choose_spec.1
  have pick_eq (t : T) : F (pick t) = (t : X) := (pre t).choose_spec.2
  have hn : InternalEpsilonNet P r U (T.attach.image pick) := by
    constructor
    · intro c hc
      obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hc
      exact pick_mem t
    · intro x hx
      obtain ⟨t,ht,hxt⟩ := hT.2 (F x) ⟨x,hx,rfl⟩
      refine ⟨pick ⟨t,ht⟩,Finset.mem_image_of_mem _ (Finset.mem_attach _ _),
        h x hx _ (pick_mem ⟨t,ht⟩) ?_⟩
      rwa [pick_eq]
  exact (cover_le_card hn).trans (by
    exact_mod_cast (Finset.card_image_le (s := T.attach) (f := pick)).trans_eq Finset.card_attach)

theorem log2_mono : Monotone log2_ereal := by
  intro a b h
  by_cases ha : a = 0
  · simp [log2_ereal, ha]
  by_cases hb : b = ⊤
  · simp [log2_ereal, hb]
  have hb0 : b ≠ 0 := fun he => ha (nonpos_iff_eq_zero.mp (he ▸ h))
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hb h
  simp only [log2_ereal, if_neg ha, if_neg hb0, if_neg hat, if_neg hb, EReal.coe_le_coe_iff]
  exact Real.logb_le_logb_of_le (by norm_num) (ENNReal.toReal_pos ha hat)
    (ENNReal.toReal_mono hb h)

theorem metric_entropy_mono_cover (h : covering_number P r U ≤ covering_number Q s B) :
    metric_entropy P r U ≤ metric_entropy Q s B := log2_mono h

theorem entropy_eq_coe (hn : U.Nonempty) (hf : covering_number P r U < ⊤) :
    metric_entropy P r U = (Real.logb 2 (covering_number P r U).toReal : EReal) := by
  have h0 := (zero_lt_one.trans_le (one_le_covering_number_of_nonempty P r U hn)).ne'
  simp [metric_entropy, log2_ereal, h0, hf.ne]

theorem entropy_top_iff (hn : U.Nonempty) :
    metric_entropy P r U = ⊤ ↔ covering_number P r U = ⊤ := by
  constructor
  · intro h
    by_contra ht
    rw [entropy_eq_coe hn (lt_top_iff_ne_top.mpr ht)] at h
    exact EReal.coe_ne_top _ h
  · intro h
    simp [metric_entropy, log2_ereal, h]

def GapDefined (f : Operator X bot) (P Q : X → X → ℝ≥0∞) (U : Set X)
    (r : ℝ≥0∞) : Prop :=
  covering_number P r U < ⊤ ∨ covering_number Q r (f.func '' U) < ⊤

noncomputable def entropyGap (f : Operator X bot) (P Q : X → X → ℝ≥0∞)
    (U : Set X) (r : ℝ≥0∞) (_h : GapDefined f P Q U r) : EReal :=
  metric_entropy P r U - metric_entropy Q r (f.func '' U)

theorem entropyGap_cases (hn : U.Nonempty) (h : GapDefined f P Q U r) :
    (covering_number P r U = ⊤ → entropyGap f P Q U r h = ⊤) ∧
    (covering_number Q r (f.func '' U) = ⊤ → entropyGap f P Q U r h = ⊥) ∧
    (covering_number P r U < ⊤ → covering_number Q r (f.func '' U) < ⊤ →
      ∃ a : ℝ, entropyGap f P Q U r h = a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hp
    have hq := h.resolve_left (fun hl => hl.ne hp)
    rw [entropyGap, (entropy_top_iff hn).mpr hp, entropy_eq_coe (hn.image _) hq]
    exact EReal.top_sub_coe _
  · intro hq
    rw [entropyGap, (entropy_top_iff (hn.image _)).mpr hq, EReal.sub_top]
  · intro hp hq
    rw [entropyGap, entropy_eq_coe hn hp, entropy_eq_coe (hn.image _) hq, ← EReal.coe_sub]
    exact ⟨_, rfl⟩

theorem entropyGap_sign (hn : U.Nonempty) (h : GapDefined f P Q U r) :
    let e := entropyGap f P Q U r h
    let a := metric_entropy P r U
    let b := metric_entropy Q r (f.func '' U)
    (0 < e ↔ b < a) ∧ (e < 0 ↔ a < b) ∧ (e = 0 ↔ a = b) := by
  dsimp
  by_cases hp : covering_number P r U = ⊤
  · have hq := h.resolve_left fun hl => hl.ne hp
    rw [(entropyGap_cases hn h).1 hp, (entropy_top_iff hn).mpr hp, entropy_eq_coe (hn.image _) hq]
    simp
  · by_cases hq : covering_number Q r (f.func '' U) = ⊤
    · rw [(entropyGap_cases hn h).2.1 hq, (entropy_top_iff (hn.image _)).mpr hq,
        entropy_eq_coe hn (lt_top_iff_ne_top.mpr hp)]
      simp
    · rw [entropyGap, entropy_eq_coe hn (lt_top_iff_ne_top.mpr hp),
        entropy_eq_coe (hn.image _) (lt_top_iff_ne_top.mpr hq), ← EReal.coe_sub]
      rw [← EReal.coe_zero]
      simp only [EReal.coe_lt_coe_iff, EReal.coe_eq_coe_iff, sub_pos, sub_neg, sub_eq_zero, and_self]

theorem threshold_cover (hA : A ⊆ dom f) (hn : A.Nonempty) (hBA : B ⊆ A)
    (hr : FinitePositive r) (hs : FinitePositive s) (h : r ≤ uniform f P Q A A) :
    covering_number Q s (f.func '' B) ≤ covering_number P r B := by
  apply cover_push
  intro x hx c hc hxc
  have hm := threshold_fiber hA hn hr h (hBA hc) (show x ∈ ball P c r ∩ A from ⟨hxc,hBA hx⟩)
  exact hm.2.trans_lt hs.1

theorem threshold_entropy (hA : A ⊆ dom f) (hn : A.Nonempty) (hBA : B ⊆ A)
    (_hB : B.Nonempty) (hr : FinitePositive r) (hs : FinitePositive s)
    (h : r ≤ uniform f P Q A A) :
    metric_entropy Q s (f.func '' B) ≤ metric_entropy P r B :=
  metric_entropy_mono_cover (threshold_cover hA hn hBA hr hs h)

theorem cover_const_image (hn : U.Nonempty) (hr : 0 < r)
    (h : ∀ x ∈ U, ∀ y ∈ U, Q (f.func x) (f.func y) = 0) :
    covering_number Q r (f.func '' U) = 1 := by
  obtain ⟨c,hc⟩ := hn
  refine cover_single_center ⟨f.func c,⟨c,hc,rfl⟩,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  exact (h x hx c hc).trans_lt hr

theorem small_cover (hA : A ⊆ dom f) (hn : A.Nonempty)
    {s t : ℝ≥0∞} (hs : FinitePositive s) (ht : FinitePositive t)
    (hd : diameter P A < s) (hst : s ≤ t) (h : t ≤ uniform f P Q A A)
    (hr : FinitePositive r) : covering_number Q r (f.func '' A) = 1 :=
  cover_const_image hn hr.1 ((small_iff hA hn hs ht hd hst).mp h)

theorem finite_gap (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {J K : Set I}
    (hJ : J.Nonempty) (hK : K.Nonempty) (_hU : U ⊆ dom f) (hn : U.Nonempty)
    (hf : U.Finite) (hr : FinitePositive r) :
    let P := subfamily_pseudometric d J
    let Q := subfamily_pseudometric d K
    let V := f.func '' U
    0 < covering_number P r U ∧ 0 < covering_number Q r V ∧
    covering_number P r U < ⊤ ∧ covering_number Q r V < ⊤ ∧
    (∃ a : ℝ, metric_entropy P r U = a) ∧
    (∃ b : ℝ, metric_entropy Q r V = b) ∧ GapDefined f P Q U r := by
  dsimp
  have hp := cover_finite hf (fun x _ => (subfamily_pseudometric_is_extended d J hJ hd).dist_self x) hr.1
  have hq := cover_finite (hf.image f.func)
    (fun x _ => (subfamily_pseudometric_is_extended d K hK hd).dist_self x) hr.1
  exact ⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ hn),
    zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ (hn.image _)),
    hp, hq, ⟨_,entropy_eq_coe hn hp⟩, ⟨_,entropy_eq_coe (hn.image _) hq⟩, Or.inl hp⟩

theorem const_gap (_hU : U ⊆ dom f) (hn : U.Nonempty) (hr : FinitePositive r)
    (hc : j ∈ Const d f U) :
    covering_number (d j) r (f.func '' U) = 1 ∧
    metric_entropy (d j) r (f.func '' U) = 0 ∧
    ∃ h : GapDefined f (d j) (d j) U r,
      entropyGap f (d j) (d j) U r h = metric_entropy (d j) r U := by
  have hc' := cover_const_image hn hr.1 hc
  have he : metric_entropy (d j) r (f.func '' U) = 0 := by
    simp [metric_entropy, log2_ereal, hc', Real.logb_one]
  refine ⟨hc', he, Or.inr (hc'.trans_lt (by simp)), ?_⟩
  simp [entropyGap, he, sub_eq_add_neg]

theorem ident_cover (hd : ExtendedPseudoMetric X bot (d j))
    (hU : U ⊆ dom f) (_hn : U.Nonempty) (_hr : FinitePositive r)
    (hi : j ∈ Ident d f U) :
    covering_number (d j) r (f.func '' U) = covering_number (d j) r U ∧
    metric_entropy (d j) r (f.func '' U) = metric_entropy (d j) r U := by
  have he := ident_distance hd hU hi
  have hc : covering_number (d j) r (f.func '' U) = covering_number (d j) r U :=
    le_antisymm (cover_push f.func fun x hx c hc h => (he x hx c hc).trans_lt h)
      (cover_pull f.func fun x hx c hc h => (he x hx c hc).symm.trans_lt h)
  exact ⟨hc,congrArg log2_ereal hc⟩

theorem equal_cover_gap (hn : U.Nonempty)
    (he : covering_number P r U = covering_number Q r (f.func '' U))
    (hg : GapDefined f P Q U r) : entropyGap f P Q U r hg = 0 := by
  have hp : covering_number P r U < ⊤ := hg.elim id (fun h => he ▸ h)
  have he' : metric_entropy P r U = metric_entropy Q r (f.func '' U) :=
    congrArg log2_ereal he
  rw [entropyGap, ← he', entropy_eq_coe hn hp, ← EReal.coe_sub, sub_self]
  rfl

theorem ident_gap (hd : ExtendedPseudoMetric X bot (d j)) (hU : U ⊆ dom f)
    (hn : U.Nonempty) (hr : FinitePositive r) (hi : j ∈ Ident d f U)
    (hg : GapDefined f (d j) (d j) U r) : entropyGap f (d j) (d j) U r hg = 0 :=
  equal_cover_gap hn (ident_cover hd hU hn hr hi).1.symm hg

theorem lip_cover {L : ℝ≥0∞} (hL : FinitePositive L)
    (h : ∀ x ∈ U, ∀ y ∈ U, Q (f.func x) (f.func y) ≤ L * P x y) :
    covering_number Q r (f.func '' U) ≤ covering_number P (r / L) U := by
  apply cover_push
  intro x hx y hy he
  have hm := (ENNReal.lt_div_iff_mul_lt (Or.inl hL.1.ne') (Or.inl hL.2.ne)).mp he
  exact (h x hx y hy).trans_lt (by simpa [mul_comm] using hm)

theorem finitePositive_div {L : ℝ≥0∞} (hr : FinitePositive r) (hL : FinitePositive L) :
    FinitePositive (r / L) :=
  ⟨ENNReal.div_pos hr.1.ne' hL.2.ne, ENNReal.div_lt_top hr.2.ne hL.1.ne'⟩

theorem lip_gap {L : ℝ≥0∞} (_hU : U ⊆ dom f) (hn : U.Nonempty)
    (ht : TotallyBoundedAt P U) (hr : FinitePositive r) (hL : FinitePositive L)
    (h : ∀ x ∈ U, ∀ y ∈ U, Q (f.func x) (f.func y) ≤ L * P x y) :
    (∃ a : ℝ, metric_entropy P r U = a) ∧ (∃ b : ℝ, metric_entropy Q r (f.func '' U) = b) ∧
    ∃ hg : GapDefined f P Q U r,
      metric_entropy P r U - metric_entropy P (r / L) U ≤ entropyGap f P Q U r hg := by
  have hc := lip_cover (r := r) hL h
  have hf := hc.trans_lt (ht _ (finitePositive_div hr hL))
  exact ⟨⟨_,entropy_eq_coe hn (ht r hr)⟩,⟨_,entropy_eq_coe (hn.image _) hf⟩,
    Or.inl (ht r hr), EReal.sub_le_sub le_rfl (metric_entropy_mono_cover hc)⟩

theorem colip_cover [Fintype I] {K : I → I → ℝ≥0∞}
    (hK : IsCoLipMatrix d f U K) (hpos : FinitePositive (K i j)) :
    covering_number (d i) (r / K i j) U ≤ covering_number (d j) r (f.func '' U) := by
  apply cover_pull
  intro x hx c hc hxc
  have h := (Finset.single_le_sum (f := fun k => K k j * d k x c)
    (fun _ _ => zero_le _) (Finset.mem_univ i)).trans (hK.2.2 x hx c hc j)
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl hpos.1.ne') (Or.inl hpos.2.ne)).mpr
  simpa [mul_comm] using h.trans_lt hxc

theorem colip_gap [Fintype I] {K : I → I → ℝ≥0∞}
    (hK : IsCoLipMatrix d f U K) (hpos : FinitePositive (K i j))
    (hr : FinitePositive r) (ht : TotallyBoundedAt (d i) U) :
    (∃ a : ℝ, metric_entropy (d i) r U = a) ∧
    (∃ b : ℝ, metric_entropy (d i) (r / K i j) U = b) ∧
    ∃ hg : GapDefined f (d i) (d j) U r,
      entropyGap f (d i) (d j) U r hg ≤
        metric_entropy (d i) r U - metric_entropy (d i) (r / K i j) U := by
  exact ⟨⟨_,entropy_eq_coe hK.1 (ht r hr)⟩,
    ⟨_,entropy_eq_coe hK.1 (ht _ (finitePositive_div hr hpos))⟩, Or.inl (ht r hr),
    EReal.sub_le_sub le_rfl (metric_entropy_mono_cover (colip_cover hK hpos))⟩

end Chapter
