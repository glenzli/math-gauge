import Chapter3.Radius
import Mathlib.Data.EReal.Operations

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
noncomputable section
variable {X I : Type} {bot : X}

def internallyTotallyBounded (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number d r U < ⊤

theorem internal_cover_correspondence (d : X → X → ENNReal) (r : ENNReal)
    (U : Set X) (S : Finset X) :
    InternalEpsilonNet d r U S ↔ (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ (↑S : Set X), ball d c r := by
  simp [InternalEpsilonNet, ball, subset_def]

theorem covering_minimum (d : X → X → ENNReal) (r : ENNReal) (U : Set X) :
    (covering_number d r U = ⊤ ↔ ¬ ∃ S, InternalEpsilonNet d r U S) ∧
    ((∃ S, InternalEpsilonNet d r U S) → ∃ S, InternalEpsilonNet d r U S ∧
      covering_number d r U = (S.card : ENNReal) ∧
      ∀ T, InternalEpsilonNet d r U T → S.card ≤ T.card) :=
  ⟨covering_number_eq_top_iff d r U, covering_number_attained d r U⟩

theorem cover_push (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    (delta eps : ENNReal)
    (h : ∀ x ∈ U, ∀ y ∈ U, din x y < delta → dout (f x) (f y) < eps) :
    covering_number dout eps (f '' U) ≤ covering_number din delta U := by
  classical
  apply le_iInf
  intro S
  apply le_iInf
  intro hS
  have hnet : InternalEpsilonNet dout eps (f '' U) (S.image f) := by
    constructor
    · intro z hz
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact mem_image_of_mem _ (hS.1 hx)
    · rintro _ ⟨x,hx,rfl⟩
      obtain ⟨c,hc,hd⟩ := hS.2 x hx
      exact ⟨f c, Finset.mem_image.mpr ⟨c,hc,rfl⟩, h x hx c (hS.1 hc) hd⟩
  calc
    covering_number dout eps (f '' U) ≤ ((S.image f).card : ENNReal) :=
      iInf_le_of_le (S.image f) (iInf_le_of_le hnet le_rfl)
    _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le

def preimagePoint (f : X → X) (U : Set X) (fallback : X) (z : X) : X :=
  by classical exact if h : z ∈ f '' U then Classical.choose h else fallback
theorem preimagePoint_spec (f : X → X) (U : Set X) (fallback : X) {z : X}
    (hz : z ∈ f '' U) : preimagePoint f U fallback z ∈ U ∧ f (preimagePoint f U fallback z) = z := by
  simp only [preimagePoint, dif_pos hz]
  exact Classical.choose_spec hz

theorem cover_pull (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    (fallback : X) (delta eps : ENNReal)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f x) (f y) < eps → din x y < delta) :
    covering_number din delta U ≤ covering_number dout eps (f '' U) := by
  classical
  apply le_iInf
  intro T
  apply le_iInf
  intro hT
  let p := preimagePoint f U fallback
  have hp : ∀ t ∈ T, p t ∈ U ∧ f (p t) = t :=
    fun t ht => preimagePoint_spec f U fallback (hT.1 ht)
  have hnet : InternalEpsilonNet din delta U (T.image p) := by
    constructor
    · intro c hc
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hc
      exact (hp t ht).1
    · intro x hx
      obtain ⟨t,ht,hclose⟩ := hT.2 (f x) (mem_image_of_mem _ hx)
      refine ⟨p t, Finset.mem_image.mpr ⟨t,ht,rfl⟩, h x hx _ (hp t ht).1 ?_⟩
      rwa [(hp t ht).2]
  calc
    covering_number din delta U ≤ ((T.image p).card : ENNReal) :=
      iInf_le_of_le (T.image p) (iInf_le_of_le hnet le_rfl)
    _ ≤ (T.card : ENNReal) := by exact_mod_cast Finset.card_image_le

theorem cover_image_isometry (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    (fallback : X) (eps : ENNReal)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f x) (f y) = din x y) :
    covering_number dout eps (f '' U) = covering_number din eps U := by
  apply le_antisymm
  · apply cover_push
    intro x hx y hy hxy
    rwa [h x hx y hy]
  · apply cover_pull _ _ _ _ fallback
    intro x hx y hy hxy
    rwa [h x hx y hy] at hxy

theorem cover_one_of_zero (d : X → X → ENNReal) (U : Set X)
    (hne : U.Nonempty) {eps : ENNReal} (heps : 0 < eps)
    (hz : ∀ x ∈ U, ∀ y ∈ U, d x y = 0) : covering_number d eps U = 1 := by
  classical
  obtain ⟨c,hc⟩ := hne
  apply le_antisymm _ (one_le_covering_number_of_nonempty d eps U ⟨c,hc⟩)
  have hnet : InternalEpsilonNet d eps U {c} := by
    constructor
    · simpa using hc
    · intro x hx
      exact ⟨c, Finset.mem_singleton_self c, by rwa [hz x hx c hc]⟩
  exact iInf_le_of_le {c} (iInf_le_of_le hnet (by simp))

theorem threshold_fiber (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {tau : ENNReal} (h : tau ≤ uniformRadius din dout f A A)
    {y : X} (hy : y ∈ A) :
    ball din y tau ∩ A ⊆ {x | x ∈ A ∧ dout (f.func x) (f.func y) = 0} := by
  rintro x ⟨hxy,hx⟩
  exact ⟨hx, uniform_rule din dout f A A hx hy (hxy.trans_le h)⟩

theorem threshold_cover (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {B : Set X} (hBA : B ⊆ A) {tau eps : ENNReal}
    (heps : 0 < eps) (hr : tau ≤ uniformRadius din dout f A A) :
    covering_number dout eps (f.func '' B) ≤ covering_number din tau B := by
  apply cover_push
  intro x hx y hy hxy
  rwa [uniform_rule din dout f A A (hBA hx) (hBA hy) (hxy.trans_le hr)]

theorem small_domain_cover (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (hne : A.Nonempty) {ts tn eps : ENNReal}
    (hs : diameter din A < ts) (hst : ts ≤ tn)
    (hn : tn ≤ uniformRadius din dout f A A) (he : 0 < eps) :
    covering_number dout eps (f.func '' A) = 1 := by
  apply cover_one_of_zero _ _ (hne.image _) he
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  exact (small_domain_iff din dout f A hs hst).mp hn x hx y hy

theorem log2_mono : Monotone log2_ereal := by
  intro a b hab
  by_cases ha : a = 0
  · simp [log2_ereal,ha]
  by_cases hb : b = ⊤
  · simp [log2_ereal,hb]
  have hb0 : b ≠ 0 := fun hz => ha (le_antisymm (hz ▸ hab) (zero_le _))
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hb hab
  simp only [log2_ereal, if_neg ha, if_neg hb0, if_neg hb, if_neg hat]
  exact EReal.coe_le_coe_iff.mpr (Real.logb_le_logb_of_le one_lt_two
    (ENNReal.toReal_pos ha hat) (ENNReal.toReal_mono hb hab))

@[simp] theorem log2_one : log2_ereal 1 = 0 := by
  norm_num [log2_ereal]

theorem threshold_entropy (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {B : Set X} (hBA : B ⊆ A) {tau eps : ENNReal}
    (heps : 0 < eps) (hr : tau ≤ uniformRadius din dout f A A) :
    metric_entropy dout eps (f.func '' B) ≤ metric_entropy din tau B :=
  log2_mono (threshold_cover din dout f A hBA heps hr)

theorem finite_cover (d : X → X → ENNReal) (hself : ∀ x, d x x = 0)
    (U : Set X) (hfin : U.Finite) {eps : ENNReal} (heps : 0 < eps) :
    covering_number d eps U < ⊤ := by
  classical
  have hnet : InternalEpsilonNet d eps U hfin.toFinset := by
    constructor
    · simp
    · intro x hx
      exact ⟨x, hfin.mem_toFinset.mpr hx, by rwa [hself]⟩
  exact (iInf_le_of_le hfin.toFinset (iInf_le_of_le hnet le_rfl)).trans_lt
    (ENNReal.natCast_lt_top _)

theorem entropy_finite (d : X → X → ENNReal) (eps : ENNReal) (U : Set X)
    (hne : U.Nonempty) (hfin : covering_number d eps U < ⊤) :
    ∃ r : ℝ, metric_entropy d eps U = (r : EReal) := by
  have hz : covering_number d eps U ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_covering_number_of_nonempty d eps U hne))
  exact ⟨Real.logb 2 (covering_number d eps U).toReal,
    by simp [metric_entropy,log2_ereal,hz,ne_of_lt hfin]⟩

def entropyDifferenceDefined (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) : Prop :=
  U.Nonempty ∧ U ⊆ dom f ∧ 0 < eps ∧ eps < ⊤ ∧
    (covering_number din eps U < ⊤ ∨ covering_number dout eps (f.func '' U) < ⊤)
def entropyDifference (din dout : X → X → ENNReal) (f : Operator X bot)
    (eps : ENNReal) (U : Set X) (_h : entropyDifferenceDefined din dout f eps U) : EReal :=
  metric_entropy din eps U - metric_entropy dout eps (f.func '' U)

theorem finite_entropy_difference (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) (hne : U.Nonempty) (hdom : U ⊆ dom f) (hfin : U.Finite)
    (J K : Set I) {eps : ENNReal} (heps : 0 < eps) (hef : eps < ⊤) :
    entropyDifferenceDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f eps U ∧
    (∃ r : ℝ, metric_entropy (subfamily_pseudometric d J) eps U = (r : EReal)) ∧
    (∃ r : ℝ, metric_entropy (subfamily_pseudometric d K) eps (f.func '' U) = (r : EReal)) := by
  have hself : ∀ H x, subfamily_pseudometric d H x x = 0 :=
    fun H x => (sup_zero_iff _ _ _ _).mpr (fun j _ => (hd j).dist_self x)
  have h1 := finite_cover _ (hself J) U hfin heps
  have h2 := finite_cover _ (hself K) (f.func '' U) (hfin.image f.func) heps
  exact ⟨⟨hne,hdom,heps,hef,Or.inl h1⟩, entropy_finite _ _ _ hne h1,
    entropy_finite _ _ _ (hne.image _) h2⟩

theorem constant_entropy (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hne : U.Nonempty) {j : I} (hj : j ∈ constComponents d f U)
    {eps : ENNReal} (he : 0 < eps) :
    covering_number (d j) eps (f.func '' U) = 1 ∧ metric_entropy (d j) eps (f.func '' U) = 0 := by
  have hc : covering_number (d j) eps (f.func '' U) = 1 :=
    cover_one_of_zero _ _ (hne.image _) he (by
      rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩; exact hj x hx y hy)
  exact ⟨hc, by simp [metric_entropy,hc]⟩

theorem constant_difference (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) {j : I} (hj : j ∈ constComponents d f U)
    {eps : ENNReal} (h : entropyDifferenceDefined (d j) (d j) f eps U) :
    entropyDifference (d j) (d j) f eps U h = metric_entropy (d j) eps U := by
  simp [entropyDifference, (constant_entropy d f U h.1 hj h.2.2.1).2]

theorem identity_entropy (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {j : I} (hj : j ∈ idComponents d f U) (eps : ENNReal) :
    covering_number (d j) eps (f.func '' U) = covering_number (d j) eps U ∧
    metric_entropy (d j) eps (f.func '' U) = metric_entropy (d j) eps U := by
  have hc := cover_image_isometry (d j) (d j) f.func U bot eps (id_isometry d hd f U hj)
  exact ⟨hc, congrArg log2_ereal hc⟩

theorem identity_difference (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {j : I} (hj : j ∈ idComponents d f U) {eps : ENNReal}
    (h : entropyDifferenceDefined (d j) (d j) f eps U) :
    entropyDifference (d j) (d j) f eps U h = 0 := by
  have hc := (identity_entropy d hd f U hj eps).1
  have he := (identity_entropy d hd f U hj eps).2
  have hf : covering_number (d j) eps U < ⊤ :=
    h.2.2.2.2.elim id (fun hh => by rwa [hc] at hh)
  obtain ⟨r,hr⟩ := entropy_finite (d j) eps U h.1 hf
  simp [entropyDifference,he,hr]

theorem scalar_cover_lip (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    {L eps : ENNReal} (hL : 0 < L) (hLf : L < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f x) (f y) ≤ L * din x y) :
    covering_number dout eps (f '' U) ≤ covering_number din (eps/L) U := by
  apply cover_push
  intro x hx y hy hxy
  exact (h x hx y hy).trans_lt (ENNReal.mul_lt_of_lt_div' hxy)

theorem scalar_cover_colip (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    (fallback : X) {K eps : ENNReal} (hK : 0 < K) (hKf : K < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, K * din x y ≤ dout (f x) (f y)) :
    covering_number din (eps/K) U ≤ covering_number dout eps (f '' U) := by
  apply cover_pull _ _ _ _ fallback
  intro x hx y hy hxy
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl (ne_of_gt hK)) (Or.inl (ne_of_lt hKf))).mpr
  simpa [mul_comm] using (h x hx y hy).trans_lt hxy

theorem matrix_cover_colip [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) (hf : K i j < ⊤) (eps : ENNReal) :
    covering_number (d i) (eps / K i j) U ≤ covering_number (d j) eps (f.func '' U) := by
  apply scalar_cover_colip _ _ _ _ bot hp hf
  intro x hx y hy
  exact (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)).trans
    (hK.2.2 x hx y hy j)

theorem lip_entropy_bound (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hne : U.Nonempty) (hdom : U ⊆ dom f)
    (htb : internallyTotallyBounded din U) {eps L : ENNReal}
    (he : 0 < eps) (hef : eps < ⊤) (hL : 0 < L) (hLf : L < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) ≤ L * din x y) :
    ∃ hdef : entropyDifferenceDefined din dout f eps U,
      (∃ a : ℝ, metric_entropy din eps U = (a : EReal)) ∧
      (∃ b : ℝ, metric_entropy dout eps (f.func '' U) = (b : EReal)) ∧
      metric_entropy din eps U - metric_entropy din (eps/L) U ≤
        entropyDifference din dout f eps U hdef := by
  have hi := htb eps he hef
  have hs := htb (eps/L) (ENNReal.div_pos (ne_of_gt he) (ne_of_lt hLf))
    (lt_top_iff_ne_top.mpr (ENNReal.div_ne_top (ne_of_lt hef) (ne_of_gt hL)))
  have hc := scalar_cover_lip din dout f.func U (eps := eps) hL hLf h
  have ho := hc.trans_lt hs
  exact ⟨⟨hne,hdom,he,hef,Or.inl hi⟩, entropy_finite _ _ _ hne hi,
    entropy_finite _ _ _ (hne.image _) ho, EReal.sub_le_sub le_rfl (log2_mono hc)⟩

theorem colip_entropy_bound [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) (hf : K i j < ⊤)
    (htb : internallyTotallyBounded (d i) U) {eps : ENNReal} (he : 0 < eps) (hef : eps < ⊤) :
    ∃ hdef : entropyDifferenceDefined (d i) (d j) f eps U,
      entropyDifference (d i) (d j) f eps U hdef ≤
        metric_entropy (d i) eps U - metric_entropy (d i) (eps/K i j) U := by
  exact ⟨⟨hK.1,hK.2.1,he,hef,Or.inl (htb eps he hef)⟩,
    EReal.sub_le_sub le_rfl (log2_mono (matrix_cover_colip d f U K i j hK hp hf eps))⟩

theorem factor_scalar_bound (d : X → X → ENNReal) (f g : Operator X bot) (U : Set X)
    (T : (f.func '' U) → X) (hT : ∀ x : U, T (imageInclusion f U x) = g.func x)
    {K L : ENNReal} (hK : 0 < K) (hKf : K < ⊤) (hLf : L < ⊤)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d x y ≤ d (f.func x) (f.func y))
    (hli : ∀ x ∈ U, ∀ y ∈ U, d (g.func x) (g.func y) ≤ L * d x y) :
    ∀ a b : f.func '' U, d (T a) (T b) ≤ (L/K) * d a b := by
  rintro ⟨_,x,hx,rfl⟩ ⟨_,y,hy,rfl⟩
  rw [show T ⟨f.func x,mem_image_of_mem _ hx⟩ = g.func x from hT ⟨x,hx⟩,
      show T ⟨f.func y,mem_image_of_mem _ hy⟩ = g.func y from hT ⟨y,hy⟩]
  have hd : d x y ≤ d (f.func x) (f.func y) / K :=
    (ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hK)) (Or.inl (ne_of_lt hKf))).mpr
      (by simpa [mul_comm] using hco x hx y hy)
  calc
    d (g.func x) (g.func y) ≤ L * d x y := hli x hx y hy
    _ ≤ L * (d (f.func x) (f.func y) / K) := mul_le_mul_left' hd L
    _ = (L/K) * d (f.func x) (f.func y) := by simp [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]

end
end Chapter3
