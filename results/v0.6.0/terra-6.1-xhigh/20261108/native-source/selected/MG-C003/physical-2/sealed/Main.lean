import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.decoupling

namespace Chapter03

open Set
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X}

def constComponents (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) : Set I :=
  {i | ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = 0}

def idComponents (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) : Set I :=
  {i | i ∉ constComponents d f U ∧ ∀ x ∈ U, d i (f.func x) x = 0}

def activeComponents (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) : Set I :=
  (constComponents d f U ∪ idComponents d f U)ᶜ

def fiber (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ subfamily_pseudometric d J (f.func x) y = 0}

def pointRelation (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f.func p.1 = f.func p.2}

def zeroRelation (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f.func p.1) (f.func p.2)}

def fiberPreorder (d : I → X → X → ENNReal) (U : Set X)
    (f g : Operator X bot) : Prop := zeroRelation d f U ⊆ zeroRelation d g U

def admissibleRadius (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) (r : ENNReal) : Prop :=
  0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, din x y < r → dout (f.func x) (f.func y) = 0

noncomputable def nullRadius (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) (U : Set X) : ENNReal :=
  ⨆ r : ENNReal, ⨆ (_ : admissibleRadius din dout f y U r), r

noncomputable def uniformRadius (din dout : X → X → ENNReal)
    (f : Operator X bot) (A U : Set X) : ENNReal :=
  ⨅ y ∈ A, nullRadius din dout f y U

noncomputable def nullMatrix (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (i j : I) : ENNReal := uniformRadius (d i) (d j) f U U

structure InputScale (X I : Type) where
  scale : I → Set X → ENNReal
  mono : ∀ i A B, A.Nonempty → B.Nonempty → A ⊆ B → scale i A ≤ scale i B

noncomputable def diameter (d : X → X → ENNReal) (A : Set X) : ENNReal :=
  ⨆ x ∈ A, ⨆ y ∈ A, d x y

noncomputable def thresholdType (sigma r ts tn : ENNReal) : Bool × Bool :=
  (decide (sigma < ts), decide (tn ≤ r))

def totallyBoundedInternal (d : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ ε : ENNReal, 0 < ε → ε < ⊤ → covering_number d ε U < ⊤

def entropyDifferenceDefined (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J K : Set I) (ε : ENNReal) : Prop :=
  covering_number (subfamily_pseudometric d J) ε U < ⊤ ∨
  covering_number (subfamily_pseudometric d K) ε (f.func '' U) < ⊤

noncomputable def entropyDifference (d : I → X → X → ENNReal) (f : Operator X bot)
    (U : Set X) (J K : Set I) (ε : ENNReal)
    (_h : entropyDifferenceDefined d f U J K ε) : EReal :=
  subfamily_metric_entropy d J ε U - subfamily_metric_entropy d K ε (f.func '' U)

theorem const_zero_row [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I) (h : i ∈ constComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y := by
  intro x hx y hy
  simp [h x hx y hy]

theorem const_colip_zero [Fintype I] (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (K : I → I → ENNReal) (i k : I)
    (h : i ∈ constComponents d f U) (hK : IsCoLipMatrix d f U K)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U) (hp : 0 < d k x y) : K k i = 0 :=
  colip_entry_eq_zero_of_output_zero_input_pos d f U K k i x y hK hx hy (h x hx y hy) hp

theorem const_outer (d : I → X → X → ENNReal) (f g : Operator X bot)
    (U : Set X) (i : I) (h : i ∈ constComponents d g (f.func '' U)) :
    i ∈ constComponents d (g * f) U := by
  intro x hx y hy
  exact h (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩

theorem zero_replace (d : X → X → ENNReal)
    (symm : ∀ x y, d x y = d y x)
    (tri : ∀ x y z, d x z ≤ d x y + d y z)
    {a b c : X} (hab : d a b = 0) : d a c = d b c := by
  apply le_antisymm
  · simpa [hab] using tri a b c
  · have hba : d b a = 0 := by rw [symm, hab]
    simpa [hba] using tri b a c

theorem id_preserves_dist (d : I → X → X → ENNReal)
    (f : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i)) (h : i ∈ idComponents d f U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (f.func x) (f.func y) = d i x y := by
  intro x hx y hy
  calc
    d i (f.func x) (f.func y) = d i x (f.func y) := zero_replace (d i) hd.symm hd.triangle (h.2 x hx)
    _ = d i (f.func y) x := hd.symm _ _
    _ = d i y x := zero_replace (d i) hd.symm hd.triangle (h.2 y hy)
    _ = d i x y := hd.symm _ _

theorem fiber_iff_components (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) (x : X) :
    x ∈ fiber d f J y U ↔ x ∈ U ∧ ∀ j ∈ J, d j (f.func x) y = 0 := by
  change (x ∈ U ∧ (⨆ j : {j // j ∈ J}, d j.1 (f.func x) y) = 0) ↔ _
  constructor
  · rintro ⟨hx, hz⟩
    refine ⟨hx, ?_⟩
    intro j hj
    apply le_antisymm _ (zero_le _)
    simpa [hz] using (le_iSup (fun k : {j // j ∈ J} => d k.1 (f.func x) y) ⟨j, hj⟩)
  · rintro ⟨hx, hz⟩
    refine ⟨hx, le_antisymm ?_ (zero_le _)⟩
    exact iSup_le fun j => le_of_eq (hz j.1 j.2)

theorem fiber_antitone (d : I → X → X → ENNReal) (f : Operator X bot)
    {J K : Set I} (hJK : J ⊆ K) (y : X) (U : Set X) :
    fiber d f K y U ⊆ fiber d f J y U := by
  intro x hx
  rw [fiber_iff_components] at hx ⊢
  exact ⟨hx.1, fun j hj => hx.2 j (hJK hj)⟩

theorem fiber_singleton (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) :
    fiber d f {i} y U = {x | x ∈ U ∧ d i (f.func x) y = 0} := by
  ext x
  simp [fiber_iff_components]

theorem fiber_cover (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (U : Set X) (self : ∀ i x, d i x x = 0) :
    ∀ x ∈ U, ∃ y ∈ f.func '' U, x ∈ fiber d f J y U := by
  intro x hx
  refine ⟨f.func x, ⟨x, hx, rfl⟩, ?_⟩
  rw [fiber_iff_components]
  exact ⟨hx, fun i _ => self i _⟩

theorem fiber_image_nonempty (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (U : Set X) (self : ∀ i x, d i x x = 0)
    {y : X} (hy : y ∈ f.func '' U) : (fiber d f J y U).Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨x, (fiber_iff_components d f J _ U x).2 ⟨hx, fun i _ => self i _⟩⟩

theorem fiber_intersection (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y : X) (U : Set X) :
    fiber d f J y U = U ∩ ⋂ j ∈ J, fiber d f {j} y U := by
  ext x
  simp only [fiber_iff_components, Set.mem_inter_iff, Set.mem_iInter]
  constructor
  · rintro ⟨hx, hz⟩
    refine ⟨hx, fun j hj => ⟨hx, ?_⟩⟩
    intro k hk
    have hkj : k = j := by simpa using hk
    subst k
    exact hz j hj
  · rintro ⟨hx, hz⟩
    exact ⟨hx, fun j hj => (hz j hj).2 j (by simp)⟩

theorem fiber_intersection_nonempty (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (hJ : J.Nonempty) (y : X) (U : Set X) :
    fiber d f J y U = ⋂ j ∈ J, fiber d f {j} y U := by
  rw [fiber_intersection]
  apply Set.inter_eq_right.mpr
  intro x hx
  obtain ⟨j, hj⟩ := hJ
  have h := Set.mem_iInter.mp (Set.mem_iInter.mp hx j) hj
  exact ((fiber_iff_components d f {j} y U x).mp h).1

theorem fiber_full_subset (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) : fiber d f Set.univ y U ⊆ fiber d f {i} y U :=
  fiber_antitone d f (Set.subset_univ _) y U

theorem fiber_target_zero (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y z : X) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hyz : ∀ i ∈ J, d i y z = 0) : fiber d f J y U = fiber d f J z U := by
  ext x
  rw [fiber_iff_components, fiber_iff_components]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  have heq : d i (f.func x) y = d i (f.func x) z := by
    rw [(hd i).symm (f.func x) y, (hd i).symm (f.func x) z]
    exact zero_replace (d i) (hd i).symm (hd i).triangle (hyz i hi)
  rw [heq]

theorem fiber_target_subfamily_zero (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y z : X) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hyz : subfamily_pseudometric d J y z = 0) :
    fiber d f J y U = fiber d f J z U := by
  apply fiber_target_zero d f J y z U hd
  intro i hi
  apply le_antisymm _ (zero_le _)
  have h := le_iSup (fun k : {k // k ∈ J} => d k.1 y z) ⟨i, hi⟩
  change (⨆ k : {k // k ∈ J}, d k.1 y z) = 0 at hyz
  rw [hyz] at h
  exact h

theorem fiber_equal_or_disjoint (d : I → X → X → ENNReal) (f : Operator X bot)
    (J : Set I) (y z : X) (U : Set X)
    (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) :
    fiber d f J y U = fiber d f J z U ∨ Disjoint (fiber d f J y U) (fiber d f J z U) := by
  classical
  by_cases h : Disjoint (fiber d f J y U) (fiber d f J z U)
  · exact Or.inr h
  · left
    have hne : (fiber d f J y U ∩ fiber d f J z U).Nonempty :=
      Set.not_disjoint_iff_nonempty_inter.mp h
    obtain ⟨x, hxy, hxz⟩ := hne
    have hy := ((fiber_iff_components d f J y U x).mp hxy).2
    have hz := ((fiber_iff_components d f J z U x).mp hxz).2
    apply fiber_target_zero d f J y z U hd
    intro i hi
    apply le_antisymm _ (zero_le _)
    have htri := (hd i).triangle y (f.func x) z
    simpa [(hd i).symm y (f.func x), hy i hi, hz i hi] using htri

theorem fiber_id_target (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (y : X) (U : Set X) (hd : ExtendedPseudoMetric X bot (d i))
    (h : i ∈ idComponents d f U) :
    fiber d f {i} y U = {x | x ∈ U ∧ d i x y = 0} := by
  rw [fiber_singleton]
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hz⟩
    exact ⟨hx, (zero_replace (d i) hd.symm hd.triangle (h.2 x hx)).symm ▸ hz⟩
  · rintro ⟨hx, hz⟩
    exact ⟨hx, (zero_replace (d i) hd.symm hd.triangle (h.2 x hx)) ▸ hz⟩

theorem fiber_const_image (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (U : Set X) (h : i ∈ constComponents d f U)
    {y : X} (hy : y ∈ f.func '' U) : fiber d f {i} y U = U := by
  obtain ⟨z, hz, rfl⟩ := hy
  rw [fiber_singleton]
  ext x
  simp only [Set.mem_setOf_eq]
  exact ⟨And.left, fun hx => ⟨hx, h x hx z hz⟩⟩

theorem fiber_const_away (d : I → X → X → ENNReal) (f : Operator X bot)
    (i : I) (U : Set X) (h : i ∈ constComponents d f U)
    (hd : ExtendedPseudoMetric X bot (d i)) {y y₀ : X}
    (hy₀ : y₀ ∈ f.func '' U) (hpos : 0 < d i y y₀) : fiber d f {i} y U = ∅ := by
  obtain ⟨z, hz, rfl⟩ := hy₀
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  rw [fiber_singleton] at hx
  have htri := hd.triangle y (f.func x) (f.func z)
  have hzero : d i y (f.func z) = 0 := by
    apply le_antisymm _ (zero_le _)
    simpa [hd.symm y (f.func x), hx.2, h x hx.1 z hz] using htri
  exact (ne_of_gt hpos) hzero

theorem diameter_mono (d : X → X → ENNReal) {A B : Set X} (h : A ⊆ B) :
    diameter d A ≤ diameter d B := by
  unfold diameter
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  exact le_iSup_of_le x (le_iSup_of_le (h hx) (le_iSup_of_le y (le_iSup_of_le (h hy) le_rfl)))

theorem scale_mono (s : InputScale X I) (i : I) {A B : Set X}
    (hA : A.Nonempty) (hB : B.Nonempty) (h : A ⊆ B) (t : ENNReal) :
    s.scale i A ≤ s.scale i B ∧ (s.scale i B < t → s.scale i A < t) := by
  exact ⟨s.mono i A B hA hB h, fun ht => lt_of_le_of_lt (s.mono i A B hA hB h) ht⟩

theorem threshold_first_mono (a t t' : ENNReal) (h : t ≤ t') :
    a < t → a < t' := fun ha => lt_of_lt_of_le ha h

theorem threshold_second_mono (a t t' : ENNReal) (h : t ≤ t') :
    t' ≤ a → t ≤ a := fun ha => le_trans h ha

theorem const_comp_lip [Fintype I] (d : I → X → X → ENNReal)
    (f g : Operator X bot) (U : Set X) (L : I → I → ENNReal) (j : I)
    (hc : j ∈ constComponents d f U) (hl : IsLipMatrix d g (f.func '' U) L)
    (hrow : ∀ k, k ≠ j → L k j = 0) : j ∈ constComponents d (g * f) U := by
  intro x hx y hy
  apply le_antisymm _ (zero_le _)
  have h := lip_bound_of_single_input_row d g (f.func '' U) L j j hl hrow
    (f.func x) ⟨x, hx, rfl⟩ (f.func y) ⟨y, hy, rfl⟩
  simpa [hc x hx y hy] using h

theorem fiberPreorder_refl (d : I → X → X → ENNReal) (U : Set X)
    (f : Operator X bot) : fiberPreorder d U f f := Set.Subset.rfl

theorem fiberPreorder_trans (d : I → X → X → ENNReal) (U : Set X)
    (f g h : Operator X bot) : fiberPreorder d U f g → fiberPreorder d U g h →
      fiberPreorder d U f h := Set.Subset.trans

def HasImageFactor (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : {y // y ∈ f.func '' U} → X,
    ∀ x (hx : x ∈ U), T ⟨f.func x, ⟨x, hx, rfl⟩⟩ = g.func x

theorem image_factor_iff (f g : Operator X bot) (U : Set X) :
    HasImageFactor f g U ↔ pointRelation f U ⊆ pointRelation g U := by
  classical
  constructor
  · rintro ⟨T, hT⟩ ⟨x, y⟩ ⟨hx, hy, heq⟩
    refine ⟨hx, hy, ?_⟩
    have he : (⟨f.func x, ⟨x, hx, rfl⟩⟩ : {z // z ∈ f.func '' U}) =
        ⟨f.func y, ⟨y, hy, rfl⟩⟩ := Subtype.ext heq
    calc
      g.func x = T ⟨f.func x, ⟨x, hx, rfl⟩⟩ := (hT x hx).symm
      _ = T ⟨f.func y, ⟨y, hy, rfl⟩⟩ := congrArg T he
      _ = g.func y := hT y hy
  · intro h
    let T : {y // y ∈ f.func '' U} → X := fun y => g.func (Classical.choose y.property)
    refine ⟨T, ?_⟩
    intro x hx
    let z : {y // y ∈ f.func '' U} := ⟨f.func x, ⟨x, hx, rfl⟩⟩
    have hs := Classical.choose_spec z.property
    have hr : (Classical.choose z.property, x) ∈ pointRelation f U :=
      ⟨hs.1, hx, hs.2⟩
    exact (h hr).2.2

theorem image_factor_both_iff (f g : Operator X bot) (U : Set X) :
    (HasImageFactor f g U ∧ HasImageFactor g f U) ↔
      pointRelation f U = pointRelation g U := by
  rw [image_factor_iff, image_factor_iff, Set.Subset.antisymm_iff]

theorem radius_mono_domain (din dout : X → X → ENNReal) (f : Operator X bot)
    (y : X) {A B : Set X} (hBA : B ⊆ A) :
    nullRadius din dout f y A ≤ nullRadius din dout f y B := by
  unfold nullRadius
  apply iSup_le
  intro r
  apply iSup_le
  intro hr
  apply le_iSup_of_le r
  have hb : admissibleRadius din dout f y B r :=
    ⟨hr.1, hr.2.1, fun x hx => hr.2.2 x (hBA hx)⟩
  exact le_iSup (fun _ : admissibleRadius din dout f y B r => r) hb

theorem uniform_mono_domain (din dout : X → X → ENNReal) (f : Operator X bot)
    {A B : Set X} (hBA : B ⊆ A) :
    uniformRadius din dout f A A ≤ uniformRadius din dout f B B := by
  unfold uniformRadius
  apply le_iInf
  intro y
  apply le_iInf
  intro hy
  exact (iInf_le_of_le y (iInf_le_of_le (hBA hy) le_rfl)).trans
    (radius_mono_domain din dout f y hBA)

end Chapter03
