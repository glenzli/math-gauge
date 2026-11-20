import Radii
import Mathlib.Data.EReal.Operations
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

abbrev cov := @covering_number
abbrev ent := @metric_entropy
def TB (p : D X) (U : Set X) := ∀ r, PosFin r → cov p r U < ⊤
def Defined (p q : D X) (f : X → X) (U : Set X) (e : ENNReal) :=
  cov p e U < ⊤ ∨ cov q e (f '' U) < ⊤
def delta (p q : D X) (f : X → X) (U : Set X) (e : ENNReal) (_ : Defined p q f U e) :=
  ent p e U - ent q e (f '' U)

variable {p q : D X} {f : X → X} {U A B : Set X} {e r L : ENNReal}

theorem internal_spec (S : Finset X) :
    InternalEpsilonNet p e U S ↔ (S : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ S, ball p c e := by
  simp [InternalEpsilonNet, Set.subset_def, ball]

theorem tb_spec : TB p U ↔ ∀ r, PosFin r → ∃ S, InternalEpsilonNet p r U S := by
  simp [TB,cov,lt_top_iff_ne_top,covering_number_eq_top_iff]

theorem net_bound {S : Finset X} (h : InternalEpsilonNet p e U S) : cov p e U ≤ S.card :=
  iInf_le_of_le S (iInf_le_of_le h le_rfl)

theorem push_net {S : Finset X} (hs : InternalEpsilonNet p r U S)
    (h : ∀ x ∈ U, ∀ y ∈ U, p x y < r → q (f x) (f y) < e) :
    InternalEpsilonNet q e (f '' U) (S.image f) ∧ (S.image f).card ≤ S.card := by
  refine ⟨⟨?_,?_⟩, Finset.card_image_le⟩
  · intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact ⟨x,hs.1 hx,rfl⟩
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,hy,hxy⟩ := hs.2 x hx
    exact ⟨_,Finset.mem_image_of_mem _ hy,h x hx y (hs.1 hy) hxy⟩

theorem push_cover (h : ∀ x ∈ U, ∀ y ∈ U, p x y < r → q (f x) (f y) < e) :
    cov q e (f '' U) ≤ cov p r U := by
  refine le_iInf fun S => le_iInf fun hs => ?_
  obtain ⟨hnet,hcard⟩ := push_net hs h
  exact (net_bound hnet).trans (by exact_mod_cast hcard)

def repr (f : X → X) (U : Set X) (z : X) := if hz : z ∈ f '' U then hz.choose else z
theorem repr_spec (z : X) (hz : z ∈ f '' U) : repr f U z ∈ U ∧ f (repr f U z) = z := by
  simpa [repr,hz] using hz.choose_spec

theorem pull_net {T : Finset X} (ht : InternalEpsilonNet q e (f '' U) T)
    (h : ∀ x ∈ U, ∀ y ∈ U, q (f x) (f y) < e → p x y < r) :
    InternalEpsilonNet p r U (T.image (repr f U)) ∧ (T.image (repr f U)).card ≤ T.card := by
  refine ⟨⟨?_,?_⟩,Finset.card_image_le⟩
  · intro c hc
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
    exact (repr_spec z (ht.1 hz)).1
  · intro x hx
    obtain ⟨z,hz,hxz⟩ := ht.2 _ ⟨x,hx,rfl⟩
    obtain ⟨hc,he⟩ := repr_spec z (ht.1 hz)
    exact ⟨_,Finset.mem_image_of_mem _ hz,h x hx _ hc (he.symm ▸ hxz)⟩

theorem pull_cover (h : ∀ x ∈ U, ∀ y ∈ U, q (f x) (f y) < e → p x y < r) :
    cov p r U ≤ cov q e (f '' U) := by
  refine le_iInf fun T => le_iInf fun ht => ?_
  obtain ⟨hnet,hcard⟩ := pull_net ht h
  exact (net_bound hnet).trans (by exact_mod_cast hcard)

theorem log_mono : Monotone log2_ereal := by
  intro a b h
  by_cases ha : a = 0
  · simp [log2_ereal,ha]
  by_cases hb : b = ⊤
  · simp [log2_ereal,hb]
  have ha' : a ≠ ⊤ := ne_top_of_le_ne_top hb h
  have hb' : b ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.mpr ha) h).ne'
  simp [log2_ereal,ha,hb,ha',hb',Real.logb_le_logb_of_le one_lt_two
    (ENNReal.toReal_pos ha ha') (ENNReal.toReal_mono hb h)]

theorem threshold_cover (hBA : B ⊆ A) (hr : r ≤ uniform p q f A A) (he : 0 < e) :
    cov q e (f '' B) ≤ cov p r B :=
  push_cover fun _ hx _ hy hp => (uniform_zero (hBA hx) (hBA hy) (hp.trans_le hr)).symm ▸ he

theorem threshold_entropy (hBA : B ⊆ A) (hr : r ≤ uniform p q f A A) (he : 0 < e) :
    ent q e (f '' B) ≤ ent p r B := log_mono (threshold_cover hBA hr he)

theorem one_cover (hu : U.Nonempty) (hc : Const q f U) (he : 0 < e) :
    cov q e (f '' U) = 1 := by
  obtain ⟨y,hy⟩ := hu
  apply le_antisymm _ (one_le_covering_number_of_nonempty q e (f '' U) ⟨f y,y,hy,rfl⟩)
  have h : InternalEpsilonNet q e (f '' U) {f y} := by
    constructor
    · simpa using (mem_image_of_mem f hy)
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨_,Finset.mem_singleton_self _,(hc x hx y hy).symm ▸ he⟩
  simpa using net_bound h

theorem small_cover (hu : U.Nonempty) {t u : ENNReal} (hd : diameter p U < t)
    (ht : t ≤ u) (hn : u ≤ uniform p q f U U) (he : 0 < e) : cov q e (f '' U) = 1 :=
  one_cover hu ((small_iff hd ht).mp hn) he

theorem finite_entropy (hu : U.Nonempty) (h : cov p e U < ⊤) :
    ∃ a : ℝ, ent p e U = a := by
  have h0 := (zero_lt_one.trans_le (one_le_covering_number_of_nonempty p e U hu)).ne'
  exact ⟨Real.logb 2 (cov p e U).toReal,by simp [ent,metric_entropy,log2_ereal,h0,h.ne]⟩

theorem finite_cover (hd : ∀ x, p x x = 0) (hu : U.Finite) (he : 0 < e) : cov p e U < ⊤ := by
  have h : InternalEpsilonNet p e U hu.toFinset :=
    ⟨by simp,fun x hx => ⟨x,hu.mem_toFinset.mpr hx,(hd x).symm ▸ he⟩⟩
  exact (net_bound h).trans_lt (ENNReal.natCast_lt_top _)

theorem finite_ends {d : I → D X} (hd : ∀ i, ExtendedPseudoMetric X b (d i))
    (J K : Set I) (hj : J.Nonempty) (hk : K.Nonempty) (hu : U.Nonempty) (hf : U.Finite)
    (f : X → X) (he : PosFin e) :
    (0 < cov (subD d J) e U ∧ cov (subD d J) e U < ⊤) ∧
    (0 < cov (subD d K) e (f '' U) ∧ cov (subD d K) e (f '' U) < ⊤) ∧
    (∃ a : ℝ, ent (subD d J) e U = a) ∧ (∃ a : ℝ, ent (subD d K) e (f '' U) = a) ∧
    Defined (subD d J) (subD d K) f U e := by
  have h₁ := finite_cover (subfamily_pseudometric_is_extended d J hj hd).dist_self hf he.1
  have h₂ := finite_cover (subfamily_pseudometric_is_extended d K hk hd).dist_self (hf.image f) he.1
  exact ⟨⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ hu),h₁⟩,
    ⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ (hu.image f)),h₂⟩,
    finite_entropy hu h₁,finite_entropy (hu.image f) h₂,Or.inl h₁⟩

theorem const_delta (hu : U.Nonempty) (hc : Const p f U) (he : 0 < e) :
    cov p e (f '' U) = 1 ∧ ent p e (f '' U) = 0 ∧
    ∃ h : Defined p p f U e, delta p p f U e h = ent p e U := by
  have hn := one_cover hu hc he
  have ho : ent p e (f '' U) = 0 := by simp [ent,metric_entropy,hn,log2_ereal]
  exact ⟨hn,ho,Or.inr (hn ▸ ENNReal.one_lt_top),by simp [delta,ho]⟩

theorem ident_cover (hd : ExtendedPseudoMetric X b p) (hi : Ident p f U) :
    cov p e (f '' U) = cov p e U ∧ ent p e (f '' U) = ent p e U := by
  have h := fun {x y} (hx : x ∈ U) (hy : y ∈ U) => ident_dist hd hi hx hy
  have heq : cov p e (f '' U) = cov p e U :=
    le_antisymm (push_cover fun _ hx _ hy hh => (h hx hy).symm ▸ hh)
      (pull_cover fun _ hx _ hy hh => (h hx hy) ▸ hh)
  exact ⟨heq,congrArg log2_ereal heq⟩

theorem ident_delta (hd : ExtendedPseudoMetric X b p) (hi : Ident p f U)
    (hu : U.Nonempty) (hw : Defined p p f U e) : delta p p f U e hw = 0 := by
  obtain ⟨hn,he⟩ := ident_cover (e := e) hd hi
  obtain ⟨a,ha⟩ := finite_entropy hu (hw.elim id (hn ▸ id))
  rw [delta,he,ha,← EReal.coe_sub,sub_self,EReal.coe_zero]

theorem div_pf (he : PosFin e) (hL : PosFin L) : PosFin (e / L) :=
  ⟨ENNReal.div_pos he.1.ne' hL.2.ne, ENNReal.div_lt_top he.2.ne hL.1.ne'⟩

theorem lip_cover (hl : ∀ x ∈ U, ∀ y ∈ U, q (f x) (f y) ≤ L * p x y) (hL : PosFin L) :
    cov q e (f '' U) ≤ cov p (e / L) U :=
  push_cover fun x hx y hy h => (hl x hx y hy).trans_lt ((scaled_lt hL).mp h)

theorem lip_delta (hu : U.Nonempty) (ht : TB p U) (he : PosFin e) (hL : PosFin L)
    (hl : ∀ x ∈ U, ∀ y ∈ U, q (f x) (f y) ≤ L * p x y) :
    (∃ a : ℝ, ent p e U = a) ∧ (∃ a : ℝ, ent q e (f '' U) = a) ∧
    ∃ hw, ent p e U - ent p (e/L) U ≤ delta p q f U e hw := by
  have hh := lip_cover (e := e) hl hL
  exact ⟨finite_entropy hu (ht e he),finite_entropy (hu.image f) (hh.trans_lt (ht _ (div_pf he hL))),
    Or.inl (ht e he), EReal.sub_le_sub le_rfl (log_mono hh)⟩

theorem colip_cover [Fintype I] {d : I → D X} {F : Op b} {K : I → I → ENNReal}
    (hk : IsCoLipMatrix d F U K) {i j : I} (hp : PosFin (K i j)) :
    cov (d i) (e / K i j) U ≤ cov (d j) e (F.func '' U) := by
  apply pull_cover
  intro x hx y hy h
  apply (scaled_lt hp).mpr
  exact (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y))
    (Finset.mem_univ i)).trans_lt ((hk.2.2 x hx y hy j).trans_lt h)

theorem colip_delta [Fintype I] {d : I → D X} {F : Op b} {K : I → I → ENNReal}
    (hk : IsCoLipMatrix d F U K) {i j : I} (hp : PosFin (K i j)) (ht : TB (d i) U)
    (he : PosFin e) : ∃ hw, delta (d i) (d j) F.func U e hw ≤
      ent (d i) e U - ent (d i) (e / K i j) U :=
  ⟨Or.inl (ht e he), EReal.sub_le_sub le_rfl (log_mono (colip_cover hk hp))⟩

theorem delta_cases (hu : U.Nonempty) (hw : Defined p q f U e) :
    (cov p e U = ⊤ → delta p q f U e hw = ⊤) ∧
    (cov q e (f '' U) = ⊤ → delta p q f U e hw = ⊥) ∧
    (cov p e U < ⊤ → cov q e (f '' U) < ⊤ → ∃ a : ℝ, delta p q f U e hw = a) := by
  constructor
  · intro h
    obtain ⟨a,ha⟩ := finite_entropy (hu.image f) (hw.resolve_left (by simp [h]))
    rw [delta,ha]
    simp [ent,metric_entropy,h,log2_ereal]
  constructor
  · intro h
    simp [delta,ent,metric_entropy,h,log2_ereal,EReal.sub_top]
  · intro h k
    obtain ⟨a,ha⟩ := finite_entropy hu h
    obtain ⟨c,hc⟩ := finite_entropy (hu.image f) k
    exact ⟨a-c,by rw [delta,ha,hc,EReal.coe_sub]⟩

end
end C3
