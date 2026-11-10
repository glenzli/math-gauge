import Chapter3.Radius
import Mathlib.Data.EReal.Operations

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {bot : X}

def TotallyBoundedAt (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ r : ENNReal, 0 < r → r < ⊤ → covering_number d r U < ⊤

theorem covering_interface (d : X → X → ENNReal) (r : ENNReal) (U : Set X) :
    (covering_number d r U = ⊤ ↔ ¬ ∃ S, InternalEpsilonNet d r U S) ∧
    (∀ S, InternalEpsilonNet d r U S →
      ∃ T, InternalEpsilonNet d r U T ∧ covering_number d r U = (T.card : ENNReal) ∧
        ∀ V, InternalEpsilonNet d r U V → T.card ≤ V.card) :=
  ⟨covering_number_eq_top_iff d r U, fun S hS => covering_number_attained d r U ⟨S,hS⟩⟩

theorem cover_push (din dout : X → X → ENNReal) (f : X → X) (U : Set X)
    (ri ro : ENNReal) (h : ∀ x ∈ U, ∀ y ∈ U, din x y < ri → dout (f x) (f y) < ro) :
    covering_number dout ro (f '' U) ≤ covering_number din ri U := by
  classical
  apply le_iInf; intro S; apply le_iInf; intro hS
  have hT : InternalEpsilonNet dout ro (f '' U) (S.image f) := by
    constructor
    · intro z hz; obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
      exact ⟨x,hS.1 hx,rfl⟩
    · rintro z ⟨x,hx,rfl⟩
      obtain ⟨c,hc,hd⟩ := hS.2 x hx
      exact ⟨f c,Finset.mem_image.mpr ⟨c,hc,rfl⟩,h x hx c (hS.1 hc) hd⟩
  exact (iInf_le_of_le (S.image f) (iInf_le_of_le hT le_rfl)).trans
    (by exact_mod_cast Finset.card_image_le)

theorem cover_pull (din dout : X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (ri ro : ENNReal) (h : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) < ro → din x y < ri) :
    covering_number din ri U ≤ covering_number dout ro (f.func '' U) := by
  classical
  apply le_iInf; intro T; apply le_iInf; intro hT
  let pick : X → X := fun t => if ht : t ∈ f.func '' U then Classical.choose ht else bot
  have hp : ∀ t ∈ T, pick t ∈ U ∧ f.func (pick t) = t := by
    intro t ht
    have him := hT.1 ht
    dsimp only [pick]
    rw [dif_pos him]
    exact Classical.choose_spec him
  have hS : InternalEpsilonNet din ri U (T.image pick) := by
    constructor
    · intro z hz; obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hz; exact (hp t ht).1
    · intro x hx
      obtain ⟨t,ht,hdt⟩ := hT.2 (f.func x) ⟨x,hx,rfl⟩
      refine ⟨pick t,Finset.mem_image.mpr ⟨t,ht,rfl⟩,h x hx _ (hp t ht).1 ?_⟩
      rwa [(hp t ht).2]
  exact (iInf_le_of_le (T.image pick) (iInf_le_of_le hS le_rfl)).trans
    (by exact_mod_cast Finset.card_image_le)

theorem log2_mono : Monotone log2_ereal := by
  intro a b hab
  by_cases ha : a = 0
  · simp [log2_ereal,ha]
  have hb : b ≠ 0 := fun hb => ha (le_antisymm (hb ▸ hab) (zero_le _))
  by_cases hbt : b = ⊤
  · simp [log2_ereal,hb,hbt]
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top hbt hab
  simp only [log2_ereal,if_neg ha,if_neg hb,if_neg hat,if_neg hbt]
  exact EReal.coe_le_coe_iff.mpr (Real.logb_le_logb_of_le one_lt_two
    (ENNReal.toReal_pos ha hat) (ENNReal.toReal_mono hbt hab))

theorem cover_zero_class (d : X → X → ENNReal) (U : Set X) (hU : U.Nonempty)
    {ε : ENNReal} (hε : 0 < ε) (h : ∀ x ∈ U, ∀ y ∈ U, d x y = 0) :
    covering_number d ε U = 1 := by
  classical
  apply le_antisymm _ (one_le_covering_number_of_nonempty d ε U hU)
  obtain ⟨c,hc⟩ := hU
  have hn : InternalEpsilonNet d ε U {c} := by
    constructor
    · simpa
    · intro x hx; exact ⟨c,by simp,by rw [h x hx c hc]; exact hε⟩
  exact iInf_le_of_le {c} (iInf_le_of_le hn (by simp))

theorem threshold_cover (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (hBA : B ⊆ A) {τ ε : ENNReal}
    (hτ : τ ≤ uniformRadius din dout f A A) (hε : 0 < ε) :
    covering_number dout ε (f.func '' B) ≤ covering_number din τ B := by
  apply cover_push
  intro x hx y hy hxy
  rw [uniform_zero (hBA hx) (hBA hy) (hxy.trans_le hτ)]
  exact hε

theorem threshold_entropy (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (hBA : B ⊆ A) {τ ε : ENNReal}
    (hτ : τ ≤ uniformRadius din dout f A A) (hε : 0 < ε) :
    metric_entropy dout ε (f.func '' B) ≤ metric_entropy din τ B :=
  log2_mono (threshold_cover din dout f hBA hτ hε)

theorem constant_cover (d : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) {ε : ENNReal} (hε : 0 < ε)
    (h : ∀ x ∈ U, ∀ y ∈ U, d (f.func x) (f.func y) = 0) :
    covering_number d ε (f.func '' U) = 1 := by
  apply cover_zero_class d _ (hU.image _) hε
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩; exact h x hx y hy

def EntropyDefined (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (ε : ENNReal) : Prop :=
  covering_number din ε U < ⊤ ∨ covering_number dout ε (f.func '' U) < ⊤
noncomputable def entropyDifference (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (ε : ENNReal) (_ : EntropyDefined din dout f U ε) : EReal :=
  metric_entropy din ε U - metric_entropy dout ε (f.func '' U)

theorem entropy_finite (d : X → X → ENNReal) (U : Set X) (hU : U.Nonempty)
    (ε : ENNReal) (hf : covering_number d ε U < ⊤) :
    metric_entropy d ε U = (Real.logb 2 (covering_number d ε U).toReal : EReal) := by
  have hz := ne_of_gt (zero_lt_one.trans_le (one_le_covering_number_of_nonempty d ε U hU))
  simp [metric_entropy,log2_ereal,hz,ne_of_lt hf]

theorem entropy_top (d : X → X → ENNReal) (U : Set X) (ε : ENNReal)
    (h : covering_number d ε U = ⊤) : metric_entropy d ε U = ⊤ := by
  simp [metric_entropy,log2_ereal,h]

theorem entropy_difference_infinite (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) (ε : ENNReal) (hD : EntropyDefined din dout f U ε) :
    (covering_number din ε U = ⊤ → entropyDifference din dout f U ε hD = ⊤) ∧
    (covering_number dout ε (f.func '' U) = ⊤ → entropyDifference din dout f U ε hD = ⊥) := by
  constructor
  · intro hin
    have hf : covering_number dout ε (f.func '' U) < ⊤ := hD.resolve_left (by simp [hin])
    simp [entropyDifference,entropy_top din U ε hin,entropy_finite dout _ (hU.image _) ε hf]
  · intro hout
    have hf : covering_number din ε U < ⊤ := hD.resolve_right (by simp [hout])
    simp [entropyDifference,entropy_top dout _ ε hout,entropy_finite din U hU ε hf]

theorem finite_cover (d : X → X → ENNReal) (hself : ∀ x, d x x = 0)
    (U : Set X) (hU : U.Finite) {ε : ENNReal} (hε : 0 < ε) : covering_number d ε U < ⊤ := by
  classical
  have hnet : InternalEpsilonNet d ε U hU.toFinset := by
    constructor
    · simp
    · intro x hx; exact ⟨x,by simpa,by rw [hself]; exact hε⟩
  exact lt_of_le_of_lt (iInf_le_of_le hU.toFinset (iInf_le_of_le hnet le_rfl))
    (ENNReal.natCast_lt_top _)

theorem finite_entropy_difference (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) (hfin : U.Finite) (J K : Set I)
    {ε : ENNReal} (hε : 0 < ε) :
    (1 ≤ covering_number (subfamily_pseudometric d J) ε U ∧
      covering_number (subfamily_pseudometric d J) ε U < ⊤) ∧
    (1 ≤ covering_number (subfamily_pseudometric d K) ε (f.func '' U) ∧
      covering_number (subfamily_pseudometric d K) ε (f.func '' U) < ⊤) ∧
    ∃ hD : EntropyDefined (subfamily_pseudometric d J) (subfamily_pseudometric d K) f U ε,
      ∃ a b : ℝ, metric_entropy (subfamily_pseudometric d J) ε U = a ∧
        metric_entropy (subfamily_pseudometric d K) ε (f.func '' U) = b ∧
        entropyDifference (subfamily_pseudometric d J) (subfamily_pseudometric d K) f U ε hD = (a-b : ℝ) := by
  have hs : ∀ L x, subfamily_pseudometric d L x x = 0 :=
    fun L x => (subfamily_zero d L x x).mpr (fun i _ => (hd i).dist_self x)
  have hi := finite_cover _ (hs J) U hfin hε
  have ho := finite_cover _ (hs K) _ (hfin.image f.func) hε
  refine ⟨⟨one_le_covering_number_of_nonempty _ _ _ hU,hi⟩,
    ⟨one_le_covering_number_of_nonempty _ _ _ (hU.image _),ho⟩,Or.inl hi,_,_,
    entropy_finite _ _ hU ε hi,entropy_finite _ _ (hU.image _) ε ho,?_⟩
  simp [entropyDifference,entropy_finite _ _ hU ε hi,entropy_finite _ _ (hU.image _) ε ho]

theorem const_entropy (d : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hU : U.Nonempty) {ε : ENNReal} (hε : 0 < ε)
    (h : ∀ x ∈ U, ∀ y ∈ U, d (f.func x) (f.func y) = 0) :
    covering_number d ε (f.func '' U) = 1 ∧ metric_entropy d ε (f.func '' U) = 0 ∧
    ∃ hD : EntropyDefined d d f U ε, entropyDifference d d f U ε hD = metric_entropy d ε U := by
  have hc := constant_cover d f U hU hε h
  have he : metric_entropy d ε (f.func '' U) = 0 := by simp [metric_entropy,log2_ereal,hc]
  refine ⟨hc,he,Or.inr (hc ▸ ENNReal.one_lt_top),?_⟩
  simp [entropyDifference,he]

theorem isometric_cover (d : X → X → ENNReal) (f : Operator X bot) (U : Set X) (ε : ENNReal)
    (h : ∀ x ∈ U, ∀ y ∈ U, d (f.func x) (f.func y) = d x y) :
    covering_number d ε (f.func '' U) = covering_number d ε U := by
  apply le_antisymm
  · exact cover_push d d f.func U ε ε (fun x hx y hy ht => by rwa [h x hx y hy])
  · exact cover_pull d d f U ε ε (fun x hx y hy ht => by rwa [h x hx y hy] at ht)

theorem id_entropy (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    (ε : ENNReal) {j : I} (hj : j ∈ idComp d f U) :
    covering_number (d j) ε (f.func '' U) = covering_number (d j) ε U ∧
    metric_entropy (d j) ε (f.func '' U) = metric_entropy (d j) ε U := by
  have hc := isometric_cover (d j) f U ε (fun _ hx _ hy => id_distance d hd hj hx hy)
  exact ⟨hc,congrArg log2_ereal hc⟩

theorem id_entropy_difference (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X)
    (hU : U.Nonempty) (ε : ENNReal) {j : I} (hj : j ∈ idComp d f U)
    (hD : EntropyDefined (d j) (d j) f U ε) : entropyDifference (d j) (d j) f U ε hD = 0 := by
  have hh := id_entropy d hd f U ε hj
  have hf : covering_number (d j) ε U < ⊤ := by
    rcases hD with h | h
    · exact h
    · rwa [hh.1] at h
  simp [entropyDifference,hh.2,entropy_finite (d j) U hU ε hf,← EReal.coe_sub]

theorem scalar_factor_lip (d : X → X → ENNReal) (f g : Operator X bot) (U : Set X)
    (T : (f.func '' U) → X) (hT : ∀ x : U, T (imagePoint f U x) = g.func x)
    {K L : ENNReal} (hK : K ≠ 0) (hKt : K ≠ ⊤)
    (hco : ∀ x ∈ U, ∀ y ∈ U, K * d x y ≤ d (f.func x) (f.func y))
    (hli : ∀ x ∈ U, ∀ y ∈ U, d (g.func x) (g.func y) ≤ L * d x y) :
    ∀ a b : f.func '' U, d (T a) (T b) ≤ (L/K) * d a b := by
  intro ⟨a,ha⟩ ⟨b,hb⟩
  obtain ⟨x,hx,rfl⟩ := ha
  obtain ⟨y,hy,rfl⟩ := hb
  change d (T (imagePoint f U ⟨x,hx⟩)) (T (imagePoint f U ⟨y,hy⟩)) ≤ _
  rw [hT,hT]
  calc
    _ ≤ L * d x y := hli x hx y hy
    _ ≤ L * (d (f.func x) (f.func y) / K) := by
      apply mul_le_mul_left'
      exact (ENNReal.le_div_iff_mul_le (Or.inl hK) (Or.inl hKt)).mpr (by simpa [mul_comm] using hco x hx y hy)
    _ = _ := by simp [div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm]

theorem lip_cover (din dout : X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (ε : ENNReal) {L : ENNReal} (hL : L ≠ 0) (hLt : L ≠ ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) ≤ L * din x y) :
    covering_number dout ε (f.func '' U) ≤ covering_number din (ε/L) U := by
  apply cover_push
  intro x hx y hy hxy
  apply (h x hx y hy).trans_lt
  simpa [mul_comm] using (ENNReal.lt_div_iff_mul_lt (Or.inl hL) (Or.inl hLt)).mp hxy

theorem colip_cover [Fintype I] (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (ε : ENNReal) {K : I → I → ENNReal} (hK : IsCoLipMatrix d f U K)
    {i j : I} (hp : K i j ≠ 0) (ht : K i j ≠ ⊤) :
    covering_number (d i) (ε / K i j) U ≤ covering_number (d j) ε (f.func '' U) := by
  apply cover_pull
  intro x hx y hy hxy
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl hp) (Or.inl ht)).mpr
  rw [mul_comm]
  exact (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)).trans_lt
    ((hK.2.2 x hx y hy j).trans_lt hxy)

theorem lip_entropy_bound (din dout : X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (hU : U.Nonempty) (hTB : TotallyBoundedAt din U) {ε L : ENNReal}
    (he : 0 < ε) (het : ε < ⊤) (hL : L ≠ 0) (hLt : L ≠ ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) ≤ L * din x y) :
    covering_number dout ε (f.func '' U) < ⊤ ∧
    ∃ hD : EntropyDefined din dout f U ε,
      metric_entropy din ε U - metric_entropy din (ε/L) U ≤ entropyDifference din dout f U ε hD := by
  have hr : 0 < ε/L := ENNReal.div_pos (ne_of_gt he) hLt
  have hrt : ε/L < ⊤ := ENNReal.div_lt_top (ne_of_lt het) hL
  have hc := lip_cover din dout f U ε hL hLt h
  exact ⟨hc.trans_lt (hTB _ hr hrt),Or.inl (hTB ε he het),EReal.sub_le_sub le_rfl (log2_mono hc)⟩

theorem colip_entropy_bound [Fintype I] (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) {ε : ENNReal} (he : 0 < ε) (het : ε < ⊤)
    {K : I → I → ENNReal} (hK : IsCoLipMatrix d f U K) {i j : I}
    (hp : K i j ≠ 0) (ht : K i j ≠ ⊤) (hTB : TotallyBoundedAt (d i) U) :
    ∃ hD : EntropyDefined (d i) (d j) f U ε,
      entropyDifference (d i) (d j) f U ε hD ≤
        metric_entropy (d i) ε U - metric_entropy (d i) (ε / K i j) U :=
  ⟨Or.inl (hTB ε he het),EReal.sub_le_sub le_rfl (log2_mono (colip_cover d f U ε hK hp ht))⟩

end Chapter3
