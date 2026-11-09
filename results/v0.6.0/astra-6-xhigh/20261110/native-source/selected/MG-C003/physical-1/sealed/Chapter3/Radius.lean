import Chapter3.Core

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
variable {X I : Type} {bot : X}

def GoodRadius (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, din x y < r → dout (f.func x) (f.func y) = 0
noncomputable def radius (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) : ENNReal := sSup {r | GoodRadius din dout f U y r}
noncomputable def uniformRadius (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) : ENNReal := ⨅ y ∈ A, radius din dout f U y
noncomputable def nullMatrix (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (j i : I) : ENNReal := uniformRadius (d i) (d j) f U U

theorem radius_representation (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) : radius din dout f U y =
    sSup {r | 0 < r ∧ r < ⊤ ∧ ball din y r ∩ U ⊆ {x ∈ U | dout (f.func x) (f.func y) = 0}} := by
  unfold radius
  congr 1; ext r
  simp only [GoodRadius, mem_setOf_eq, Set.subset_def, mem_inter_iff, ball]
  aesop

theorem radius_witness {din dout : X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {y : X} {a : ENNReal} (h : a < radius din dout f U y) :
    ∃ r, GoodRadius din dout f U y r ∧ a < r := lt_sSup_iff.mp h

theorem below_radius {din dout : X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {x y : X} (hx : x ∈ U) (h : din x y < radius din dout f U y) :
    dout (f.func x) (f.func y) = 0 := by
  obtain ⟨r,hr,har⟩ := radius_witness h
  exact hr.2.2 x hx har

theorem le_radius_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) (a : ENNReal) :
    a ≤ radius din dout f U y ↔ ∀ x ∈ U, din x y < a → dout (f.func x) (f.func y) = 0 := by
  constructor
  · intro h x hx hxy; exact below_radius hx (hxy.trans_le h)
  · intro h
    apply le_of_forall_lt
    intro b hb
    obtain ⟨r,hbr,hra⟩ := exists_between hb
    exact hbr.trans_le (le_sSup (show GoodRadius din dout f U y r from
      ⟨lt_of_le_of_lt (zero_le b) hbr, hra.trans_le le_top,
        fun x hx hxr => h x hx (hxr.trans hra)⟩))

theorem goodRadius_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (y : X) (r : ENNReal) :
    GoodRadius din dout f U y r ↔ 0 < r ∧ r < ⊤ ∧ r ≤ radius din dout f U y := by
  rw [le_radius_iff]; rfl

theorem le_uniform_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) (a : ENNReal) :
    a ≤ uniformRadius din dout f A U ↔
      ∀ y ∈ A, ∀ x ∈ U, din x y < a → dout (f.func x) (f.func y) = 0 := by
  simp only [uniformRadius, le_iInf_iff, le_radius_iff]

theorem uniform_le_point (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) {y : X} (hy : y ∈ A) : uniformRadius din dout f A U ≤ radius din dout f U y :=
  iInf_le_of_le y (iInf_le_of_le hy le_rfl)

theorem constant_radii (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (h : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) = 0) :
    (∀ y ∈ U, radius din dout f U y = ⊤) ∧ uniformRadius din dout f U U = ⊤ := by
  constructor
  · intro y hy; apply top_unique
    exact (le_radius_iff _ _ _ _ _ _).mpr (fun x hx _ => h x hx y hy)
  · apply top_unique
    exact (le_uniform_iff _ _ _ _ _ _).mpr (fun y hy x hx _ => h x hx y hy)

theorem constant_subfamily_radii (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J : Set I) (i : I) (h : J ⊆ constComp d f U) :
    (∀ y ∈ U, radius (d i) (subfamily_pseudometric d J) f U y = ⊤) ∧
    uniformRadius (d i) (subfamily_pseudometric d J) f U U = ⊤ := by
  apply constant_radii
  intro x hx y hy
  exact (subfamily_zero d J _ _).mpr (fun j hj => h hj x hx y hy)

theorem id_image_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ idComp d f U) {y : X} (hy : y ∈ U) :
    fiber d f {i} (f.func y) U = {x ∈ U | d i x y = 0} := by
  rw [fiber_singleton]; ext x
  constructor <;> rintro ⟨hx,h⟩ <;> refine ⟨hx, ?_⟩
  · rwa [id_distance d hd hi hx hy] at h
  · rwa [id_distance d hd hi hx hy]

theorem id_radius_lower (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot}
    {U : Set X} {i : I} (hi : i ∈ idComp d f U) {y : X} (hy : y ∈ U)
    {r : ENNReal} (hr : 0 < r) (hfin : r < ⊤)
    (hball : ball (d i) y r ∩ U ⊆ {x ∈ U | d i x y = 0}) :
    r ≤ radius (d i) (d i) f U y ∧ 0 < r := by
  refine ⟨(le_radius_iff _ _ _ _ _ _).mpr ?_,hr⟩
  intro x hx hxy
  rw [id_distance d hd hi hx hy]
  exact (hball ⟨hxy,hx⟩).2

theorem radius_subfamily (d : I → X → X → ENNReal) (f : Operator X bot)
    (din : X → X → ENNReal) (U : Set X) (y : X) (J : Set I) :
    radius din (subfamily_pseudometric d J) f U y = ⨅ j ∈ J, radius din (d j) f U y := by
  apply le_antisymm
  · apply le_iInf; intro j; apply le_iInf; intro hj
    apply (le_radius_iff _ _ _ _ _ _).mpr
    intro x hx hxy
    exact (subfamily_zero d J _ _).mp (below_radius hx hxy) j hj
  · apply (le_radius_iff _ _ _ _ _ _).mpr
    intro x hx hxy
    apply (subfamily_zero d J _ _).mpr
    intro j hj
    exact below_radius hx (hxy.trans_le (iInf_le_of_le j (iInf_le_of_le hj le_rfl)))

theorem uniform_subfamily (d : I → X → X → ENNReal) (f : Operator X bot)
    (din : X → X → ENNReal) (A U : Set X) (J : Set I) :
    uniformRadius din (subfamily_pseudometric d J) f A U =
      ⨅ j ∈ J, uniformRadius din (d j) f A U := by
  have he : ∀ a, a ≤ uniformRadius din (subfamily_pseudometric d J) f A U ↔
      a ≤ ⨅ j ∈ J, uniformRadius din (d j) f A U := by
    intro a
    simp only [le_iInf_iff, le_uniform_iff, subfamily_zero]
    constructor
    · intro h j hj y hy x hx hxy; exact h y hy x hx hxy j hj
    · intro h y hy x hx hxy j hj; exact h j hj y hy x hx hxy
  exact le_antisymm ((he _).mp le_rfl) ((he _).mpr le_rfl)

theorem uniform_subfamily_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    (din : X → X → ENNReal) (A U : Set X) {J K : Set I} (h : J ⊆ K) :
    uniformRadius din (subfamily_pseudometric d K) f A U ≤
      uniformRadius din (subfamily_pseudometric d J) f A U := by
  rw [uniform_subfamily, uniform_subfamily]
  exact iInf_mono' (fun j => ⟨j, iInf_mono' (fun hj => ⟨h hj,le_rfl⟩)⟩)

theorem fiber_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot} {U : Set X}
    {j : I} {y z : X} (h : z ∈ fiber d f {j} (f.func y) U) : d j (f.func y) (f.func z) = 0 :=
  (hd j).symm _ _ |>.trans (h.2 j (by simp))

theorem radius_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) {f : Operator X bot} {U : Set X}
    {i j : I} {y z : X} (hz : z ∈ U)
    (h : d i y z < radius (d i) (d j) f U y) : d j (f.func y) (f.func z) = 0 := by
  rw [(hd j).symm]
  exact below_radius (din := d i) hz (by rwa [(hd i).symm])

theorem composition_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot) (U : Set X)
    (j : I) {x y : X} (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hfx : f.func x ∈ U) (hfy : f.func y ∈ U)
    (h : f.func y ∈ fiber d g {j} (g.func (f.func x)) U) :
    d j ((g * f).func x) ((g * f).func y) = 0 :=
  fiber_truncation d hd (f := g) (y := f.func x) (z := f.func y) h

theorem uniform_zero {din dout : X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h : din x y < uniformRadius din dout f U U) : dout (f.func x) (f.func y) = 0 :=
  below_radius hx (h.trans_le (uniform_le_point _ _ _ _ _ hy))

theorem output_separation {din dout : X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (h : 0 < dout (f.func x) (f.func y)) : uniformRadius din dout f U U ≤ din x y := by
  by_contra hn
  exact (ne_of_gt h) (uniform_zero hx hy (lt_of_not_ge hn))

theorem separation_witness {din dout : X → X → ENNReal} {f : Operator X bot}
    {U : Set X} {a : ENNReal} (ha : uniformRadius din dout f U U < a) :
    ∃ x ∈ U, ∃ y ∈ U, ∃ ε : ENNReal,
      0 < ε ∧ ε < ⊤ ∧ din x y < a ∧ ε ≤ dout (f.func x) (f.func y) := by
  classical
  have hn : ¬ ∀ y ∈ U, ∀ x ∈ U, din x y < a → dout (f.func x) (f.func y) = 0 :=
    fun h => (not_le_of_gt ha) ((le_uniform_iff _ _ _ _ _ _).mpr h)
  push_neg at hn
  obtain ⟨y,hy,x,hx,hxy,hout⟩ := hn
  exact ⟨x,hx,y,hy,min 1 (dout (f.func x) (f.func y)),
    lt_min zero_lt_one (pos_iff_ne_zero.mpr hout),
    (min_le_left _ _).trans_lt ENNReal.one_lt_top,hxy,min_le_right _ _⟩

theorem radius_domain_mono (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (h : B ⊆ A) (y : X) : radius din dout f A y ≤ radius din dout f B y := by
  exact (le_radius_iff _ _ _ _ _ _).mpr (fun x hx hxy => below_radius (h hx) hxy)

theorem uniform_domain_mono (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (h : B ⊆ A) : uniformRadius din dout f A A ≤ uniformRadius din dout f B B := by
  exact (le_uniform_iff _ _ _ _ _ _).mpr (fun y hy x hx hxy => uniform_zero (h hx) (h hy) hxy)

theorem compose_radius_zero (din dmid dout : X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (h : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U,
      dmid a b = 0 → dout (g.func a) (g.func b) = 0) :
    uniformRadius din dmid f U U ≤ uniformRadius din dout (g * f) U U := by
  apply (le_uniform_iff _ _ _ _ _ _).mpr
  intro y hy x hx hxy
  exact h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ (uniform_zero hx hy hxy)

theorem compose_radius_lip (din dmid dout : X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) {L : ENNReal} (hL : L ≠ 0) (hLt : L ≠ ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dmid (f.func x) (f.func y) ≤ L * din x y) :
    uniformRadius dmid dout g (f.func '' U) (f.func '' U) / L ≤
      uniformRadius din dout (g * f) U U := by
  apply (le_uniform_iff _ _ _ _ _ _).mpr
  intro y hy x hx hxy
  apply uniform_zero (show f.func x ∈ f.func '' U from ⟨x,hx,rfl⟩)
    (show f.func y ∈ f.func '' U from ⟨y,hy,rfl⟩)
  exact (h x hx y hy).trans_lt (by
    simpa [mul_comm] using (ENNReal.lt_div_iff_mul_lt (Or.inl hL) (Or.inl hLt)).mp hxy)

noncomputable def diameter (d : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d x y
theorem le_diameter (d : X → X → ENNReal) {A : Set X} {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) : d x y ≤ diameter d A :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
theorem diameter_mono (d : X → X → ENNReal) {A B : Set X} (h : A ⊆ B) :
    diameter d A ≤ diameter d B := by
  apply iSup_le; intro x; apply iSup_le; intro hx
  apply iSup_le; intro y; apply iSup_le; intro hy
  exact le_diameter d (h hx) (h hy)

structure InputScale (X I : Type) where
  value : I → {A : Set X // A.Nonempty} → ENNReal
  mono : ∀ i A B, A.val ⊆ B.val → value i A ≤ value i B
noncomputable def diameterScale (d : I → X → X → ENNReal) : InputScale X I :=
  ⟨fun i A => diameter (d i) A, fun i _ _ h => diameter_mono (d i) h⟩
noncomputable def thresholdType (s n τs τn : ENNReal) : Bool × Bool :=
  (decide (s < τs), decide (τn ≤ n))
noncomputable def channelType (σ : InputScale X I) (d : I → X → X → ENNReal)
    (f : Operator X bot) (A : {A : Set X // A.Nonempty}) (τs τn : ENNReal) (i j : I) : Bool × Bool :=
  thresholdType (σ.value i A) (nullMatrix d f A j i) τs τn

theorem threshold_cases (s n τs τn : ENNReal) :
    (thresholdType s n τs τn = (true,true) ↔ s < τs ∧ τn ≤ n) ∧
    (thresholdType s n τs τn = (true,false) ↔ s < τs ∧ n < τn) ∧
    (thresholdType s n τs τn = (false,true) ↔ τs ≤ s ∧ τn ≤ n) ∧
    (thresholdType s n τs τn = (false,false) ↔ τs ≤ s ∧ n < τn) := by
  simp [thresholdType, not_le, not_lt]

theorem threshold_scale_mono {s τ τ' : ENNReal} (h : τ ≤ τ') (hs : s < τ) : s < τ' := hs.trans_le h
theorem threshold_null_antitone {n τ τ' : ENNReal} (h : τ ≤ τ') (hn : τ' ≤ n) : τ ≤ n := h.trans hn
theorem scale_domain_mono (σ : InputScale X I) (i : I)
    (A B : {A : Set X // A.Nonempty}) (h : B.val ⊆ A.val) (τ : ENNReal) :
    σ.value i B ≤ σ.value i A ∧ (σ.value i A < τ → σ.value i B < τ) :=
  ⟨σ.mono i B A h, fun ht => (σ.mono i B A h).trans_lt ht⟩

theorem threshold_fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (A : Set X) (i j : I) {τ : ENNReal} (h : τ ≤ nullMatrix d f A j i) {y : X} (hy : y ∈ A) :
    ball (d i) y τ ∩ A ⊆ fiber d f {j} (f.func y) A := by
  intro x hx; refine ⟨hx.2, ?_⟩
  intro k hk; have : k = j := hk; subst k
  exact uniform_zero hx.2 hy (hx.1.trans_le h)

theorem small_domain_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {τs τn : ENNReal} (hs : diameter din A < τs) (hst : τs ≤ τn) :
    τn ≤ uniformRadius din dout f A A ↔ ∀ x ∈ A, ∀ y ∈ A, dout (f.func x) (f.func y) = 0 := by
  constructor
  · intro hn x hx y hy
    exact uniform_zero hx hy ((le_diameter din hx hy).trans_lt (hs.trans_le (hst.trans hn)))
  · intro h; rw [(constant_radii din dout f A h).2]; exact le_top

theorem colip_point_gap [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {K : I → I → ENNReal} {i j : I}
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    ¬ (0 < d i x y ∧ d i x y < radius (d i) (d j) f U y) := by
  rintro ⟨hpos,hlt⟩
  exact (ne_of_gt hpos) (positive_colip_entry_reflects_zero d f U K i j hK hp x hx y hy
    (below_radius hx hlt))

theorem colip_uniform_gap [Fintype I] (d : I → X → X → ENNReal)
    {f : Operator X bot} {U : Set X} {K : I → I → ENNReal} {i j : I}
    (hK : IsCoLipMatrix d f U K) (hp : 0 < K i j) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ nullMatrix d f U j i ≤ d i x y := by
  by_cases hz : d i x y = 0
  · exact Or.inl hz
  · right; by_contra hn
    exact colip_point_gap d hK hp hx hy ⟨pos_iff_ne_zero.mpr hz,
      (lt_of_not_ge hn).trans_le (uniform_le_point _ _ _ _ _ hy)⟩

end Chapter3
