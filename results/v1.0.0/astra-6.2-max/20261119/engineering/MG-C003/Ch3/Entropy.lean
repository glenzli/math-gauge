import Ch3.Scale
import Mathlib.Data.EReal.Operations

namespace MG
open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
variable {X I : Type} {b : X} {f : Op b} {p q : Dist X} {A B U : Set X} {e r L : ENNReal}
abbrev cover := @covering_number
abbrev entropy := @metric_entropy
abbrev Net := @InternalEpsilonNet
def boundedAtAll (p : Dist X) (U : Set X) := ∀ r, positiveFinite r → cover p r U < ⊤
def good (p q : Dist X) (f : Op b) (U : Set X) (e : ENNReal) :=
  cover p e U < ⊤ ∨ cover q e (f.func '' U) < ⊤
def delta (p q : Dist X) (f : Op b) (U : Set X) (e : ENNReal) (_h : good p q f U e) :=
  entropy p e U - entropy q e (f.func '' U)

def mapDelta (d : I → Dist X) (S T : Set I) (_hS : S.Nonempty) (_hT : T.Nonempty)
    (f : Op b) (U : Set X) (_hne : U.Nonempty) (_hU : U ⊆ dom f) (e : ENNReal)
    (_he : positiveFinite e) (hg : good (subdist d S) (subdist d T) f U e) :=
  delta (subdist d S) (subdist d T) f U e hg

theorem mapDelta_formula (d : I → Dist X) {S T : Set I} (hS : S.Nonempty) (hT : T.Nonempty)
    (hne : U.Nonempty) (hU : U ⊆ dom f) (he : positiveFinite e) (hg) :
    mapDelta d S T hS hT f U hne hU e he hg =
      subfamily_metric_entropy d S e U - subfamily_metric_entropy d T e (f.func '' U) := rfl

theorem netBalls {C : Finset X} : Net p e U C ↔ (C : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ C, ball p c e := by
  simp [Net,InternalEpsilonNet,ball,Set.subset_def]

theorem netUpper {C : Finset X} (hC : Net p e U C) : cover p e U ≤ C.card :=
  iInf_le_of_le C (iInf_le_of_le hC le_rfl)

theorem coverLower {n : ENNReal} (h : ∀ C : Finset X, Net p e U C → n ≤ C.card) :
    n ≤ cover p e U := le_iInf fun C => le_iInf (h C)

theorem pushNet {C : Finset X} (hC : Net p r U C)
    (h : ∀ x ∈ U, ∀ c ∈ U, p x c < r → q (f.func x) (f.func c) < e) :
    ∃ T : Finset X, Net q e (f.func '' U) T ∧ T.card ≤ C.card := by
  classical
  refine ⟨C.image f.func,⟨?_,?_⟩,Finset.card_image_le⟩
  · intro z hz
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hz
    exact mem_image_of_mem _ (hC.1 hc)
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨c,hc,hd⟩ := hC.2 x hx
    exact ⟨_,Finset.mem_image_of_mem _ hc,h _ hx _ (hC.1 hc) hd⟩

theorem pullNet {T : Finset X} (hT : Net q e (f.func '' U) T)
    (h : ∀ x ∈ U, ∀ c ∈ U, q (f.func x) (f.func c) < e → p x c < r) :
    ∃ C : Finset X, Net p r U C ∧ C.card ≤ T.card := by
  classical
  let rep (z : X) := if hz : z ∈ f.func '' U then hz.choose else b
  have spec (z) (hz : z ∈ f.func '' U) : rep z ∈ U ∧ f.func (rep z) = z := by
    simpa only [rep,dif_pos hz] using hz.choose_spec
  refine ⟨T.image rep,⟨?_,?_⟩,Finset.card_image_le⟩
  · intro c hc
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
    exact (spec _ (hT.1 hz)).1
  · intro x hx
    obtain ⟨z,hz,hd⟩ := hT.2 _ (mem_image_of_mem _ hx)
    obtain ⟨hu,hz'⟩ := spec _ (hT.1 hz)
    exact ⟨_,Finset.mem_image_of_mem _ hz,h x hx _ hu (hz'.symm ▸ hd)⟩

theorem pushCover (h : ∀ x ∈ U, ∀ c ∈ U, p x c < r → q (f.func x) (f.func c) < e) :
    cover q e (f.func '' U) ≤ cover p r U := by
  apply coverLower
  intro C hC
  obtain ⟨T,hT,hcard⟩ := pushNet hC h
  exact (netUpper hT).trans (Nat.cast_le.mpr hcard)

theorem pullCover (h : ∀ x ∈ U, ∀ c ∈ U, q (f.func x) (f.func c) < e → p x c < r) :
    cover p r U ≤ cover q e (f.func '' U) := by
  apply coverLower
  intro T hT
  obtain ⟨C,hC,hcard⟩ := pullNet hT h
  exact (netUpper hC).trans (Nat.cast_le.mpr hcard)

theorem logStrict : StrictMono log2_ereal := by
  intro a c h
  have hc := ((zero_le a).trans_lt h).ne'
  have ha := (h.trans_le le_top).ne
  by_cases h₀ : a = 0 <;> by_cases hT : c = ⊤
  all_goals simp [log2_ereal,h₀,hT,hc,ha]
  exact Real.logb_lt_logb one_lt_two (ENNReal.toReal_pos h₀ ha) ((ENNReal.toReal_lt_toReal ha hT).2 h)

theorem thresholdCover (hB : B ⊆ A) (ht : r ≤ uniform p q f A A) (he : 0 < e) :
    cover q e (f.func '' B) ≤ cover p r B :=
  pushCover fun _ hx _ hy hd => (cutUniform (hB hx) (hB hy) (hd.trans_le ht)).trans_lt he

theorem thresholdEntropy (hB : B ⊆ A) (ht : r ≤ uniform p q f A A) (he : 0 < e) :
    entropy q e (f.func '' B) ≤ entropy p r B := logStrict.monotone (thresholdCover hB ht he)

theorem coverOne (hne : U.Nonempty) {c : X} (hc : c ∈ U) (h : ∀ x ∈ U, p x c < e) :
    cover p e U = 1 := by
  classical
  have hn : Net p e U {c} :=
    ⟨by simpa using hc,fun x hx => ⟨c,Finset.mem_singleton_self _,h _ hx⟩⟩
  exact le_antisymm (by simpa using netUpper hn) (one_le_covering_number_of_nonempty _ _ _ hne)

theorem constCover (hne : U.Nonempty) (hc : Const q f U) (he : 0 < e) : cover q e (f.func '' U) = 1 := by
  obtain ⟨a,ha⟩ := hne
  apply coverOne ⟨_,mem_image_of_mem _ ha⟩ (mem_image_of_mem _ ha)
  rintro _ ⟨x,hx,rfl⟩
  exact (hc _ hx _ ha).trans_lt he

theorem smallCover (hne : U.Nonempty) {ts tn : ENNReal} (hs : diam p U < ts) (ht : ts ≤ tn)
    (hr : tn ≤ uniform p q f U U) (he : positiveFinite e) : cover q e (f.func '' U) = 1 :=
  constCover hne ((smallDomain hs ht).1 hr) he.1

theorem finiteCover (m : ExtendedPseudoMetric X b p) (hu : U.Finite) (he : 0 < e) :
    cover p e U < ⊤ := by
  classical
  have hn : Net p e U hu.toFinset :=
    ⟨by simp,fun x hx => ⟨x,hu.mem_toFinset.mpr hx,(m.dist_self _).trans_lt he⟩⟩
  exact (netUpper hn).trans_lt (ENNReal.natCast_lt_top _)

theorem finiteLog (hne : U.Nonempty) (h : cover p e U < ⊤) :
    ∃ a : ℝ, entropy p e U = a := by
  have hp := zero_lt_one.trans_le (one_le_covering_number_of_nonempty p e U hne)
  exact ⟨Real.logb 2 (cover p e U).toReal,by simp [entropy,metric_entropy,log2_ereal,hp.ne',h.ne,cover]⟩

theorem deltaBranches (hne : U.Nonempty) (hg : good p q f U e) :
    (cover p e U = ⊤ → delta p q f U e hg = ⊤) ∧
    (cover q e (f.func '' U) = ⊤ → delta p q f U e hg = ⊥) ∧
    (cover p e U < ⊤ → cover q e (f.func '' U) < ⊤ → ∃ a : ℝ, delta p q f U e hg = a) := by
  refine ⟨?_,?_,?_⟩
  · intro ht
    have ho := hg.resolve_left (not_lt_of_ge ht.ge)
    obtain ⟨a,ha⟩ := finiteLog (hne.image _) ho
    rw [delta,ha]
    simp [entropy,metric_entropy,ht,log2_ereal]
  · intro ht
    simp [delta,entropy,metric_entropy,ht,log2_ereal,EReal.sub_top]
  · intro ha hc
    obtain ⟨a,ha⟩ := finiteLog hne ha
    obtain ⟨c,hc⟩ := finiteLog (hne.image _) hc
    exact ⟨a-c,by rw [delta,ha,hc,EReal.coe_sub]⟩

theorem finiteData (mp : ExtendedPseudoMetric X b p) (mq : ExtendedPseudoMetric X b q)
    (hne : U.Nonempty) (hu : U.Finite) (he : positiveFinite e) :
    positiveFinite (cover p e U) ∧ positiveFinite (cover q e (f.func '' U)) ∧
    (∃ a : ℝ, entropy p e U = a) ∧ (∃ c : ℝ, entropy q e (f.func '' U) = c) ∧ good p q f U e := by
  have hi := finiteCover mp hu he.1
  have ho := finiteCover mq (hu.image f.func) he.1
  exact ⟨⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ hne),hi⟩,
    ⟨zero_lt_one.trans_le (one_le_covering_number_of_nonempty _ _ _ (hne.image _)),ho⟩,
    finiteLog hne hi,finiteLog (hne.image _) ho,Or.inl hi⟩

def subfamilyData (d : I → Dist X) (m : ∀ i, ExtendedPseudoMetric X b (d i))
    (S T : Set I) (hS : S.Nonempty) (hT : T.Nonempty) (hne : U.Nonempty) (hu : U.Finite) (he : positiveFinite e) :=
  @finiteData X b f (subdist d S) (subdist d T) U e
    (subfamily_pseudometric_is_extended d S hS m) (subfamily_pseudometric_is_extended d T hT m) hne hu he

theorem constDelta (hne : U.Nonempty) (hc : Const p f U) (he : 0 < e) :
    cover p e (f.func '' U) = 1 ∧ entropy p e (f.func '' U) = 0 ∧
      ∃ hg : good p p f U e, delta p p f U e hg = entropy p e U := by
  have hn := constCover hne hc he
  have hz : entropy p e (f.func '' U) = 0 := by change log2_ereal (cover p e (f.func '' U)) = 0; simp [hn,log2_ereal] 
  exact ⟨hn,hz,Or.inr (hn.trans_lt ENNReal.one_lt_top),by simp [delta,hz]⟩

theorem identCover (m : ExtendedPseudoMetric X b p) (hi : Ident p f U) :
    cover p e (f.func '' U) = cover p e U ∧ entropy p e (f.func '' U) = entropy p e U := by
  have hn := le_antisymm
    (pushCover (e := e) fun x hx y hy h => (identDist m hi hx hy).trans_lt h)
    (pullCover (r := e) fun x hx y hy h => (identDist m hi hx hy).symm.trans_lt h)
  exact ⟨hn,congrArg log2_ereal hn⟩

theorem identDelta (m : ExtendedPseudoMetric X b p) (hi : Ident p f U) (hne : U.Nonempty)
    (hg : good p p f U e) : delta p p f U e hg = 0 := by
  obtain ⟨hn,he⟩ := identCover (e := e) m hi
  have hfin : cover p e U < ⊤ := hg.elim id (hn ▸ id)
  obtain ⟨a,ha⟩ := finiteLog hne hfin
  rw [delta,he,ha,← EReal.coe_sub,sub_self,EReal.coe_zero]

theorem lipCover (_hL : positiveFinite L)
    (hl : ∀ x ∈ U, ∀ y ∈ U, q (f.func x) (f.func y) ≤ L * p x y) :
    cover q e (f.func '' U) ≤ cover p (e/L) U :=
  pushCover fun x hx y hy hd => (hl _ hx _ hy).trans_lt (by simpa [mul_comm] using ENNReal.mul_lt_of_lt_div hd)

theorem divScale (he : positiveFinite e) (hL : positiveFinite L) : positiveFinite (e/L) :=
  ⟨ENNReal.div_pos he.1.ne' hL.2.ne, ENNReal.div_lt_top he.2.ne hL.1.ne'⟩

theorem lipDelta (hu : boundedAtAll p U) (hne : U.Nonempty) (he : positiveFinite e) (hL : positiveFinite L)
    (hl : ∀ x ∈ U, ∀ y ∈ U, q (f.func x) (f.func y) ≤ L * p x y) :
    (∃ a : ℝ, entropy p e U = a) ∧ (∃ a : ℝ, entropy p (e/L) U = a) ∧
    (∃ a : ℝ, entropy q e (f.func '' U) = a) ∧ ∃ hg : good p q f U e,
      entropy p e U - entropy p (e/L) U ≤ delta p q f U e hg := by
  have hn := lipCover (e := e) hL hl
  have hs := hu _ (divScale he hL)
  exact ⟨finiteLog hne (hu e he),finiteLog hne hs,finiteLog (hne.image _) (hn.trans_lt hs),
    Or.inl (hu e he),EReal.sub_le_sub le_rfl (logStrict.monotone hn)⟩

theorem coCover [Fintype I] (d : I → Dist X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hk : positiveFinite (K i j)) :
    cover (d i) (e/K i j) U ≤ cover (d j) e (f.func '' U) := by
  apply pullCover
  intro x hx y hy hd
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl hk.1.ne') (Or.inl hk.2.ne)).2
  rw [mul_comm]
  exact (Finset.single_le_sum (f := fun k => K k j * d k x y) (fun k _ => zero_le _) (Finset.mem_univ i)).trans_lt
    ((hK.2.2 x hx y hy j).trans_lt hd)

theorem coDelta [Fintype I] (d : I → Dist X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hk : positiveFinite (K i j)) (he : positiveFinite e)
    (hu : boundedAtAll (d i) U) :
    ∃ hg : good (d i) (d j) f U e, delta (d i) (d j) f U e hg ≤ entropy (d i) e U - entropy (d i) (e/K i j) U :=
  ⟨Or.inl (hu e he),EReal.sub_le_sub le_rfl (logStrict.monotone (coCover d K i j hK hk))⟩

end
end MG
