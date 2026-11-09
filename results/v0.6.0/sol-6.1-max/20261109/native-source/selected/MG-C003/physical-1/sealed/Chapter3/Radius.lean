import Chapter3.Core

namespace Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
noncomputable section
variable {X I : Type} {bot : X}

/-- Distance to the complement of the output zero class; see `radius_eq_sSup`. -/
def radius (din dout : X → X → ENNReal) (f : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  ⨅ x ∈ U, ⨅ (_ : dout (f.func x) (f.func y) ≠ 0), din x y
def admissible (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, din x y < r → dout (f.func x) (f.func y) = 0
def uniformRadius (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) : ENNReal := ⨅ y ∈ A, radius din dout f y U
def nullMatrix (d : I → X → X → ENNReal) (f : Operator X bot) (U : Set X)
    (j i : I) : ENNReal := uniformRadius (d i) (d j) f U U

theorem le_radius_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) :
    r ≤ radius din dout f y U ↔ ∀ x ∈ U, din x y < r → dout (f.func x) (f.func y) = 0 := by
  classical
  constructor
  · intro h x hx hd
    by_contra hn
    have hh : radius din dout f y U ≤ din x y :=
      iInf_le_of_le x (iInf_le_of_le hx (iInf_le_of_le hn le_rfl))
    exact (not_lt_of_ge (h.trans hh)) hd
  · intro h
    apply le_iInf
    intro x
    apply le_iInf
    intro hx
    apply le_iInf
    intro hn
    by_contra hh
    exact hn (h x hx (lt_of_not_ge hh))

theorem radius_rule (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) {x : X} (hx : x ∈ U)
    (h : din x y < radius din dout f y U) : dout (f.func x) (f.func y) = 0 :=
  (le_radius_iff din dout f y U _).mp le_rfl x hx h

theorem radius_eq_sSup (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) :
    radius din dout f y U = sSup {r | admissible din dout f y U r} := by
  apply le_antisymm
  · apply ENNReal.le_of_forall_pos_nnreal_lt
    intro r hr hlt
    apply le_sSup
    exact ⟨by exact_mod_cast hr, ENNReal.coe_lt_top,
      (le_radius_iff din dout f y U _).mp (le_of_lt hlt)⟩
  · apply sSup_le
    intro r hr
    exact (le_radius_iff din dout f y U r).mpr hr.2.2

theorem extract_admissible (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) {a : ENNReal} (h : a < radius din dout f y U) :
    ∃ r, a < r ∧ admissible din dout f y U r := by
  obtain ⟨r, har, hrr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp h
  exact ⟨r, har, (zero_le a).trans_lt har, ENNReal.coe_lt_top,
    (le_radius_iff din dout f y U _).mp hrr.le⟩

theorem admissible_le_radius (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) {r : ENNReal} (h : admissible din dout f y U r) :
    r ≤ radius din dout f y U ∧ 0 < r :=
  ⟨(le_radius_iff din dout f y U r).mpr h.2.2, h.1⟩

theorem uniform_le_point (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) {y : X} (hy : y ∈ A) :
    uniformRadius din dout f A U ≤ radius din dout f y U :=
  iInf_le_of_le y (iInf_le_of_le hy le_rfl)

theorem uniform_rule (din dout : X → X → ENNReal) (f : Operator X bot)
    (A U : Set X) {x y : X} (hx : x ∈ U) (hy : y ∈ A)
    (h : din x y < uniformRadius din dout f A U) : dout (f.func x) (f.func y) = 0 :=
  radius_rule din dout f y U hx (h.trans_le (uniform_le_point din dout f A U hy))

theorem radius_top_of_const (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hc : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) = 0)
    {y : X} (hy : y ∈ U) : radius din dout f y U = ⊤ := by
  apply top_unique
  exact (le_radius_iff din dout f y U ⊤).mpr (fun x hx _ => hc x hx y hy)

theorem uniform_top_of_const (din dout : X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (hc : ∀ x ∈ U, ∀ y ∈ U, dout (f.func x) (f.func y) = 0) :
    uniformRadius din dout f U U = ⊤ := by
  apply top_unique
  exact le_iInf (fun y => le_iInf (fun hy => le_of_eq (radius_top_of_const din dout f U hc hy).symm))

theorem const_subfamily_fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J : Set I) (hc : J ⊆ constComponents d f U) {y : X} (hy : y ∈ U) :
    fiber d f J (f.func y) U = U := by
  ext x
  exact ⟨And.left, fun hx => ⟨hx, (sup_zero_iff _ _ _ _).mpr (fun j hj => hc hj x hx y hy)⟩⟩

theorem const_subfamily_radii (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J : Set I) (hc : J ⊆ constComponents d f U) (i : I) :
    (∀ y ∈ U, radius (d i) (subfamily_pseudometric d J) f y U = ⊤) ∧
    uniformRadius (d i) (subfamily_pseudometric d J) f U U = ⊤ := by
  have h : ∀ x ∈ U, ∀ y ∈ U, subfamily_pseudometric d J (f.func x) (f.func y) = 0 :=
    fun x hx y hy => (sup_zero_iff _ _ _ _).mpr (fun j hj => hc hj x hx y hy)
  exact ⟨fun _ hy => radius_top_of_const _ _ _ _ h hy, uniform_top_of_const _ _ _ _ h⟩

theorem id_image_fiber (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {i : I} (hi : i ∈ idComponents d f U) {y : X} (hy : y ∈ U) :
    componentFiber d f i (f.func y) U = {x | x ∈ U ∧ d i x y = 0} := by
  ext x
  constructor <;> intro hx
  · exact ⟨hx.1, (id_isometry d hd f U hi x hx.1 y hy) ▸ hx.2⟩
  · exact ⟨hx.1, (id_isometry d hd f U hi x hx.1 y hy).symm ▸ hx.2⟩

theorem id_radius_lower (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) {i : I} (hi : i ∈ idComponents d f U) {y : X} (hy : y ∈ U)
    {r : ENNReal} (hr : 0 < r) (hfin : r < ⊤)
    (h : ball (d i) y r ∩ U ⊆ {x | x ∈ U ∧ d i x y = 0}) :
    r ≤ radius (d i) (d i) f y U ∧ 0 < r := by
  apply admissible_le_radius
  refine ⟨hr, hfin, ?_⟩
  intro x hx hxy
  rw [id_isometry d hd f U hi x hx y hy]
  exact (h ⟨hxy, hx⟩).2

theorem radius_subfamily (d : I → X → X → ENNReal) (din : X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) (y : X) :
    radius din (subfamily_pseudometric d J) f y U = ⨅ j ∈ J, radius din (d j) f y U := by
  apply le_antisymm
  · apply le_iInf
    intro j
    apply le_iInf
    intro hj
    apply (le_radius_iff _ _ _ _ _ _).mpr
    intro x hx hxy
    exact (sup_zero_iff _ _ _ _).mp (radius_rule _ _ _ _ _ hx hxy) j hj
  · apply (le_radius_iff _ _ _ _ _ _).mpr
    intro x hx hxy
    apply (sup_zero_iff _ _ _ _).mpr
    intro j hj
    exact radius_rule _ _ _ _ _ hx (hxy.trans_le (iInf_le_of_le j (iInf_le_of_le hj le_rfl)))

theorem uniform_subfamily (d : I → X → X → ENNReal) (din : X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (J : Set I) :
    uniformRadius din (subfamily_pseudometric d J) f U U =
      ⨅ j ∈ J, uniformRadius din (d j) f U U := by
  simp only [uniformRadius, radius_subfamily]
  apply le_antisymm
  · exact le_iInf (fun j => le_iInf (fun hj => le_iInf (fun y => le_iInf (fun hy =>
      iInf_le_of_le y (iInf_le_of_le hy (iInf_le_of_le j (iInf_le_of_le hj le_rfl)))))))
  · exact le_iInf (fun y => le_iInf (fun hy => le_iInf (fun j => le_iInf (fun hj =>
      iInf_le_of_le j (iInf_le_of_le hj (iInf_le_of_le y (iInf_le_of_le hy le_rfl)))))))

theorem uniform_subfamily_antitone (d : I → X → X → ENNReal)
    (din : X → X → ENNReal) (f : Operator X bot) (U : Set X)
    {J K : Set I} (h : J ⊆ K) :
    uniformRadius din (subfamily_pseudometric d K) f U U ≤
      uniformRadius din (subfamily_pseudometric d J) f U U := by
  rw [uniform_subfamily, uniform_subfamily]
  exact le_iInf (fun j => le_iInf (fun hj => iInf_le_of_le j (iInf_le_of_le (h hj) le_rfl)))

theorem fiber_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) (j : I) {y z : X} (h : z ∈ componentFiber d f j (f.func y) U) :
    d j (f.func y) (f.func z) = 0 := by
  rw [(hd j).symm]
  exact h.2

theorem radius_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) (i j : I) {y z : X} (hz : z ∈ U)
    (h : d i y z < radius (d i) (d j) f y U) : d j (f.func y) (f.func z) = 0 := by
  rw [(hd j).symm]
  apply radius_rule (d i) (d j) f y U hz
  rwa [(hd i).symm]

theorem composite_fiber_truncation (d : I → X → X → ENNReal)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f g : Operator X bot)
    (V : Set X) (j : I) {x y : X} (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hfx : f.func x ∈ V) (hfy : f.func y ∈ V)
    (h : f.func y ∈ componentFiber d g j (g.func (f.func x)) V) :
    d j ((g*f).func x) ((g*f).func y) = 0 :=
  fiber_truncation d hd g V j h

theorem radius_domain_antitone (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (h : B ⊆ A) (y : X) : radius din dout f y A ≤ radius din dout f y B := by
  apply (le_radius_iff _ _ _ _ _ _).mpr
  intro x hx hxy
  exact radius_rule _ _ _ _ _ (h hx) hxy

theorem uniform_domain_antitone (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (h : B ⊆ A) : uniformRadius din dout f A A ≤ uniformRadius din dout f B B := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  exact (uniform_le_point _ _ _ _ _ (h hy)).trans (radius_domain_antitone din dout f h y)

theorem uniform_comp_zero (din dmid dout : X → X → ENNReal) (f g : Operator X bot)
    (U : Set X)
    (h : ∀ a ∈ f.func '' U, ∀ b ∈ f.func '' U, dmid a b = 0 → dout (g.func a) (g.func b) = 0) :
    uniformRadius din dmid f U U ≤ uniformRadius din dout (g*f) U U := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply (le_radius_iff _ _ _ _ _ _).mpr
  intro x hx hxy
  exact h _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)
    (uniform_rule din dmid f U U hx hy hxy)

theorem uniform_comp_lip (din dmid dout : X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) {L : ENNReal} (hL : 0 < L) (hLf : L < ⊤)
    (h : ∀ x ∈ U, ∀ y ∈ U, dmid (f.func x) (f.func y) ≤ L * din x y) :
    uniformRadius dmid dout g (f.func '' U) (f.func '' U) / L ≤
      uniformRadius din dout (g*f) U U := by
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  apply (le_radius_iff _ _ _ _ _ _).mpr
  intro x hx hxy
  exact uniform_rule dmid dout g _ _ (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)
    ((h x hx y hy).trans_lt (ENNReal.mul_lt_of_lt_div' hxy))

theorem output_separation (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {x y : X} (hx : x ∈ A) (hy : y ∈ A)
    (h : 0 < dout (f.func x) (f.func y)) : uniformRadius din dout f A A ≤ din x y := by
  by_contra hh
  exact (ne_of_gt h) (uniform_rule din dout f A A hx hy (lt_of_not_ge hh))

theorem separation_witness (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {alpha tau : ENNReal} (ha : 0 < alpha) (haf : alpha < ⊤)
    (hlo : uniformRadius din dout f A A < alpha) (hhi : alpha < tau) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ eps : ENNReal,
      0 < eps ∧ eps < ⊤ ∧ din x y < alpha ∧ eps ≤ dout (f.func x) (f.func y) := by
  classical
  obtain ⟨y, hy⟩ := iInf_lt_iff.mp hlo
  obtain ⟨hyA, hyr⟩ := iInf_lt_iff.mp hy
  have hbad : ∃ x ∈ A, din x y < alpha ∧ dout (f.func x) (f.func y) ≠ 0 := by
    by_contra hh
    push Not at hh
    have hle : alpha ≤ radius din dout f y A :=
      (le_radius_iff _ _ _ _ _ _).mpr (fun x hx hxy => hh x hx hxy)
    exact not_lt_of_ge hle hyr
  obtain ⟨x, hx, hxy, hout⟩ := hbad
  obtain ⟨eps, heps, hepsout⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (pos_iff_ne_zero.mpr hout)
  exact ⟨x, hx, y, hyA, eps, heps, ENNReal.coe_lt_top, hxy, hepsout.le⟩

def diameter (d : X → X → ENNReal) (A : Set X) : ENNReal := ⨆ x ∈ A, ⨆ y ∈ A, d x y
structure InputScales (X I : Type) where
  scale : I → {A : Set X // A.Nonempty} → ENNReal
  mono : ∀ i A B, A.1 ⊆ B.1 → scale i A ≤ scale i B
def diameterScales (d : I → X → X → ENNReal) : InputScales X I where
  scale i A := diameter (d i) A.1
  mono i A B h := iSup_le (fun x => iSup_le (fun hx => iSup_le (fun y => iSup_le (fun hy =>
    le_iSup_of_le x (le_iSup_of_le (h hx) (le_iSup_of_le y (le_iSup_of_le (h hy) le_rfl)))))))
def thresholdType (sigma n ts tn : ENNReal) : Bool × Bool := (decide (sigma < ts), decide (tn ≤ n))

theorem threshold_four (sigma n ts tn : ENNReal) :
    (thresholdType sigma n ts tn = (true,true) ↔ sigma < ts ∧ tn ≤ n) ∧
    (thresholdType sigma n ts tn = (true,false) ↔ sigma < ts ∧ n < tn) ∧
    (thresholdType sigma n ts tn = (false,true) ↔ ts ≤ sigma ∧ tn ≤ n) ∧
    (thresholdType sigma n ts tn = (false,false) ↔ ts ≤ sigma ∧ n < tn) := by
  simp [thresholdType, Prod.ext_iff, not_lt, not_le]
theorem threshold_scale_mono {sigma ts ts' : ENNReal} (h : ts ≤ ts') :
    sigma < ts → sigma < ts' := fun hh => hh.trans_le h
theorem threshold_radius_antitone {n tn tn' : ENNReal} (h : tn ≤ tn') :
    tn' ≤ n → tn ≤ n := fun hh => h.trans hh
theorem scale_domain_mono (s : InputScales X I) (i : I)
    (A B : {A : Set X // A.Nonempty}) (h : B.1 ⊆ A.1) (tau : ENNReal) :
    s.scale i B ≤ s.scale i A ∧ (s.scale i A < tau → s.scale i B < tau) :=
  ⟨s.mono i B A h, fun hh => (s.mono i B A h).trans_lt hh⟩

theorem dist_le_diameter (d : X → X → ENNReal) {A : Set X} {x y : X}
    (hx : x ∈ A) (hy : y ∈ A) : d x y ≤ diameter d A :=
  le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

theorem small_domain_iff (din dout : X → X → ENNReal) (f : Operator X bot)
    (A : Set X) {ts tn : ENNReal} (hs : diameter din A < ts) (hst : ts ≤ tn) :
    tn ≤ uniformRadius din dout f A A ↔ ∀ x ∈ A, ∀ y ∈ A, dout (f.func x) (f.func y) = 0 := by
  constructor
  · intro hn x hx y hy
    exact uniform_rule din dout f A A hx hy
      ((dist_le_diameter din hx hy).trans_lt (hs.trans_le (hst.trans hn)))
  · intro h
    rw [uniform_top_of_const din dout f A h]
    exact le_top

theorem colip_point_gap [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) :
    ¬ (0 < d i x y ∧ d i x y < radius (d i) (d j) f y U) := by
  rintro ⟨hxy, hr⟩
  exact (ne_of_gt hxy) (positive_colip_entry_reflects_zero d f U K i j hK hpos x hx y hy
    (radius_rule _ _ _ _ _ hx hr))

theorem colip_uniform_gap [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ uniformRadius (d i) (d j) f U U ≤ d i x y := by
  by_cases hz : d i x y = 0
  · exact Or.inl hz
  · right
    by_contra hn
    exact colip_point_gap d f U K i j hK hpos hx hy
      ⟨pos_iff_ne_zero.mpr hz, (lt_of_not_ge hn).trans_le (uniform_le_point _ _ _ _ _ hy)⟩

end
end Chapter3
