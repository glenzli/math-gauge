import Chapter.Fibers

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open scoped ENNReal
namespace Chapter

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {f g : Operator X bot} {U A B : Set X} {i j k : I}
variable {P Q : X → X → ℝ≥0∞} {y x : X} {r : ℝ≥0∞}

def FinitePositive (r : ℝ≥0∞) : Prop := 0 < r ∧ r < ⊤

def admissible (f : Operator X bot) (P Q : X → X → ℝ≥0∞)
    (U : Set X) (y : X) : Set ℝ≥0∞ :=
  {r | FinitePositive r ∧ ball P y r ∩ U ⊆ fiber Q f U (f.func y)}

noncomputable def radius (f : Operator X bot) (P Q : X → X → ℝ≥0∞)
    (U : Set X) (y : X) : ℝ≥0∞ := sSup (admissible f P Q U y)

noncomputable def uniform (f : Operator X bot) (P Q : X → X → ℝ≥0∞)
    (A U : Set X) : ℝ≥0∞ := ⨅ y : A, radius f P Q U y

noncomputable def nullMatrix (d : I → X → X → ℝ≥0∞)
    (f : Operator X bot) (U : Set X) (j i : I) : ℝ≥0∞ :=
  uniform f (d i) (d j) U U

theorem admissible_iff :
    r ∈ admissible f P Q U y ↔ FinitePositive r ∧
      ∀ x ∈ U, P x y < r → Q (f.func x) (f.func y) = 0 :=
  ⟨fun h => ⟨h.1, fun _ hx hd => (h.2 ⟨hd,hx⟩).2⟩,
   fun h => ⟨h.1, fun _ hx => ⟨hx.2, h.2 _ hx.2 hx.1⟩⟩⟩

theorem radius_empty (h : admissible f P Q U y = ∅) : radius f P Q U y = 0 := by
  simp [radius, h]

theorem radius_witness (h : r < radius f P Q U y) :
    ∃ s ∈ admissible f P Q U y, r < s := by
  by_contra! hn
  exact h.not_ge (sSup_le hn)

theorem radius_zero (hx : x ∈ U) (h : P x y < radius f P Q U y) :
    Q (f.func x) (f.func y) = 0 := by
  obtain ⟨s, hs, hlt⟩ := radius_witness h
  exact (admissible_iff.mp hs).2 _ hx hlt

theorem le_radius_iff :
    r ≤ radius f P Q U y ↔ ∀ x ∈ U, P x y < r → Q (f.func x) (f.func y) = 0 := by
  constructor
  · exact fun h _ hx hd => radius_zero hx (hd.trans_le h)
  · intro h
    by_contra! he
    obtain ⟨s, hs, ht⟩ := exists_between he
    have ha : s ∈ admissible f P Q U y :=
      admissible_iff.mpr ⟨⟨(zero_le _).trans_lt hs, ht.trans_le le_top⟩,
        fun x hx hd => h x hx (hd.trans ht)⟩
    exact hs.not_ge (le_sSup ha)

theorem uniform_le_point (hy : y ∈ A) : uniform f P Q A U ≤ radius f P Q U y :=
  iInf_le (fun z : A => radius f P Q U z) ⟨y,hy⟩

theorem le_uniform_iff :
    r ≤ uniform f P Q A U ↔ ∀ y ∈ A, ∀ x ∈ U, P x y < r → Q (f.func x) (f.func y) = 0 := by
  constructor
  · exact fun h y hy => le_radius_iff.mp (h.trans (uniform_le_point hy))
  · exact fun h => le_iInf fun y : A => le_radius_iff.mpr (h y y.2)

theorem uniform_eq_inf_separated :
    uniform f P Q U U =
      ⨅ y : U, ⨅ x : U, ⨅ _ : Q (f.func x) (f.func y) ≠ 0, P x y := by
  apply le_antisymm
  · refine le_iInf fun y => le_iInf fun x => le_iInf fun hn => ?_
    exact le_of_not_gt fun h => hn (le_uniform_iff.mp (le_refl (uniform f P Q U U)) (y : X) y.2 (x : X) x.2 h)
  · refine le_uniform_iff.mpr fun y hy x hx h => ?_
    by_contra hn
    have hi : (⨅ y : U, ⨅ x : U, ⨅ _ : Q (f.func x) (f.func y) ≠ 0, P x y) ≤ P x y :=
      iInf_le_of_le ⟨y,hy⟩ (iInf_le_of_le ⟨x,hx⟩ (iInf_le_of_le hn le_rfl))
    exact h.not_ge hi

theorem radius_top (h : ∀ x ∈ U, P x y < ⊤ → Q (f.func x) (f.func y) = 0) :
    radius f P Q U y = ⊤ := top_unique (le_radius_iff.mpr h)

theorem const_subfamily_fiber {J : Set I} (_hU : U ⊆ dom f) (_hJ : J.Nonempty)
    (hc : J ⊆ Const d f U) (hy : y ∈ U) :
    fiber (subfamily_pseudometric d J) f U (f.func y) = U := by
  ext x
  exact ⟨fun hx => hx.1, fun hx => ⟨hx, (subfamily_zero _ _ _ _).mpr
    fun j hj => hc hj x hx y hy⟩⟩

theorem const_subfamily_radii {J : Set I} (hU : U ⊆ dom f) (_hne : U.Nonempty)
    (hJ : J.Nonempty) (hc : J ⊆ Const d f U) (i : I) :
    (∀ y ∈ U, radius f (d i) (subfamily_pseudometric d J) U y = ⊤) ∧
    uniform f (d i) (subfamily_pseudometric d J) U U = ⊤ := by
  have hp : ∀ y ∈ U, radius f (d i) (subfamily_pseudometric d J) U y = ⊤ := by
    intro y hy
    apply radius_top
    intro x hx _
    have hm : x ∈ fiber (subfamily_pseudometric d J) f U (f.func y) :=
      (const_subfamily_fiber hU hJ hc hy).symm ▸ hx
    exact hm.2
  exact ⟨hp, top_unique (le_iInf fun y : U => (hp y y.2).ge)⟩

theorem ident_fiber_self (hd : ExtendedPseudoMetric X bot (d i)) (hU : U ⊆ dom f)
    (hi : i ∈ Ident d f U) (hy : y ∈ U) :
    fiber (d i) f U (f.func y) = {x ∈ U | d i x y = 0} := by
  ext x
  constructor <;> intro h
  · exact ⟨h.1, (ident_distance hd hU hi x h.1 y hy).symm.trans h.2⟩
  · exact ⟨h.1, (ident_distance hd hU hi x h.1 y hy).trans h.2⟩

theorem ident_radius (hd : ExtendedPseudoMetric X bot (d i)) (hU : U ⊆ dom f)
    (hi : i ∈ Ident d f U) (hy : y ∈ U) (hr : FinitePositive r)
    (h : ball (d i) y r ∩ U ⊆ {x ∈ U | d i x y = 0}) :
    r ≤ radius f (d i) (d i) U y ∧ 0 < r := by
  rw [← ident_fiber_self hd hU hi hy] at h
  exact ⟨le_sSup ⟨hr,h⟩, hr.1⟩

theorem radius_subfamily {J : Set I} (_hJ : J.Nonempty) (_hU : U ⊆ dom f) (_hy : y ∈ U) :
    radius f P (subfamily_pseudometric d J) U y = ⨅ j : J, radius f P (d j.1) U y := by
  apply le_antisymm
  · refine le_iInf fun j => le_radius_iff.mpr fun x hx hxlt => ?_
    exact (subfamily_zero _ _ _ _).mp (radius_zero hx hxlt) j.1 j.2
  · refine le_radius_iff.mpr fun x hx hxlt => (subfamily_zero _ _ _ _).mpr fun j hj => ?_
    exact radius_zero hx (hxlt.trans_le (iInf_le (fun j : J => radius f P (d j) U y) ⟨j,hj⟩))

theorem iInf_attains [Finite I] {J : Set I} (hJ : J.Nonempty) (a : J → ℝ≥0∞) :
    ∃ j : J, (⨅ k : J, a k) = a j := by
  haveI : Nonempty J := hJ.to_subtype
  obtain ⟨j,hj⟩ := Finite.exists_min a
  exact ⟨j, le_antisymm (iInf_le a j) (le_iInf hj)⟩

theorem uniform_subfamily {J : Set I} (hJ : J.Nonempty) (hU : U ⊆ dom f) :
    uniform f (d i) (subfamily_pseudometric d J) U U = ⨅ j : J, nullMatrix d f U j i := by
  unfold uniform nullMatrix
  calc
    _ = (⨅ y : U, ⨅ j : J, radius f (d i) (d j) U y) := by
      congr 1
      funext y
      exact radius_subfamily hJ hU y.2
    _ = _ := iInf_comm

theorem uniform_subfamily_antitone {J K : Set I} (hJ : J.Nonempty) (hK : K.Nonempty)
    (hU : U ⊆ dom f) (h : J ⊆ K) :
    uniform f (d i) (subfamily_pseudometric d K) U U ≤
      uniform f (d i) (subfamily_pseudometric d J) U U := by
  rw [uniform_subfamily hK hU, uniform_subfamily hJ hU]
  exact le_iInf fun j : J => iInf_le (fun k : K => nullMatrix d f U k i) ⟨j,h j.2⟩

theorem fiber_step (hQ : ExtendedPseudoMetric X bot Q) (_hU : U ⊆ dom f)
    (_hy : y ∈ U) (_hx : x ∈ U) (h : x ∈ fiber Q f U (f.func y)) :
    Q (f.func y) (f.func x) = 0 := (hQ.symm _ _).trans h.2

theorem radius_step (hP : ExtendedPseudoMetric X bot P) (hQ : ExtendedPseudoMetric X bot Q)
    (hU : U ⊆ dom f) (hy : y ∈ U) (hx : x ∈ U) (h : P y x < radius f P Q U y) :
    Q (f.func y) (f.func x) = 0 :=
  fiber_step hQ hU hy hx ⟨hx, radius_zero hx ((hP.symm x y).trans_lt h)⟩

theorem fiber_comp (hQ : ExtendedPseudoMetric X bot Q) (hU : U ⊆ dom g)
    {x y : X} (_hx : x ∈ dom f) (_hy : y ∈ dom f)
    (hx' : f.func x ∈ U) (hy' : f.func y ∈ U)
    (h : f.func y ∈ fiber Q g U (g.func (f.func x))) :
    Q ((g * f).func x) ((g * f).func y) = 0 :=
  fiber_step (f := g) hQ hU hx' hy' h

theorem radius_comp_zero (_hU : U ⊆ dom (g * f)) (_hne : U.Nonempty)
    (h : ∀ x ∈ f.func '' U, ∀ y ∈ f.func '' U,
      d k x y = 0 → d j (g.func x) (g.func y) = 0) :
    nullMatrix d f U k i ≤ nullMatrix d (g * f) U j i :=
  le_uniform_iff.mpr fun y hy x hx hxy =>
    h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ (le_uniform_iff.mp le_rfl y hy x hx hxy)

theorem radius_comp_lip (_hU : U ⊆ dom (g * f)) (_hne : U.Nonempty)
    {L : ℝ≥0∞} (hL : FinitePositive L)
    (h : ∀ x ∈ U, ∀ y ∈ U, d k (f.func x) (f.func y) ≤ L * d i x y) :
    nullMatrix d g (f.func '' U) j k / L ≤ nullMatrix d (g * f) U j i := by
  refine le_uniform_iff.mpr fun y hy x hx hxy => ?_
  have hm := (ENNReal.lt_div_iff_mul_lt (Or.inl hL.1.ne') (Or.inl hL.2.ne)).mp hxy
  rw [mul_comm] at hm
  exact le_uniform_iff.mp (le_refl (nullMatrix d g (f.func '' U) j k)) (f.func y) ⟨y,hy,rfl⟩ (f.func x) ⟨x,hx,rfl⟩
    ((h x hx y hy).trans_lt hm)

theorem radius_restrict (hBA : B ⊆ A) (_hy : y ∈ B) :
    radius f P Q A y ≤ radius f P Q B y :=
  le_radius_iff.mpr fun _ hx h => radius_zero (hBA hx) h

theorem uniform_restrict (hBA : B ⊆ A) (_hA : A ⊆ dom f) (_hn : B.Nonempty) :
    uniform f P Q A A ≤ uniform f P Q B B :=
  le_iInf fun y : B => (uniform_le_point (hBA y.2)).trans (radius_restrict hBA y.2)

theorem uniform_zero (_hA : A ⊆ dom f) (_hn : A.Nonempty)
    (hx : x ∈ A) (hy : y ∈ A) (h : P x y < uniform f P Q A A) :
    Q (f.func x) (f.func y) = 0 := le_uniform_iff.mp le_rfl y hy x hx h

theorem uniform_separation (hA : A ⊆ dom f) (hn : A.Nonempty)
    (hx : x ∈ A) (hy : y ∈ A) (h : 0 < Q (f.func x) (f.func y)) :
    uniform f P Q A A ≤ P x y :=
  le_of_not_gt fun he => h.ne' (uniform_zero hA hn hx hy he)

theorem uniform_failure (_hA : A ⊆ dom f) (_hn : A.Nonempty)
    {τ α : ℝ≥0∞} (_ht : FinitePositive τ) (_ha : FinitePositive α)
    (h : uniform f P Q A A < α) (_haτ : α < τ) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ ε, FinitePositive ε ∧ P x y < α ∧ ε ≤ Q (f.func x) (f.func y) := by
  classical
  have hbad := mt (le_uniform_iff (f := f) (P := P) (Q := Q) (A := A) (U := A) (r := α)).mpr h.not_ge
  push Not at hbad
  obtain ⟨y,hy,x,hx,hxy,hnz⟩ := hbad
  obtain ⟨ε,hε,hε'⟩ := exists_between (pos_iff_ne_zero.mpr hnz)
  exact ⟨x,hx,y,hy,ε,⟨hε,hε'.trans_le le_top⟩,hxy,hε'.le⟩

theorem threshold_fiber (hA : A ⊆ dom f) (hn : A.Nonempty)
    (_hr : FinitePositive r) (h : r ≤ uniform f P Q A A) (hy : y ∈ A) :
    ball P y r ∩ A ⊆ fiber Q f A (f.func y) :=
  fun _ hx => ⟨hx.2, uniform_zero hA hn hx.2 hy (hx.1.trans_le h)⟩

theorem point_gap [Fintype I] (_hP : ExtendedPseudoMetric X bot (d i))
    (_hQ : ExtendedPseudoMetric X bot (d j)) {K : I → I → ℝ≥0∞}
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j) (hy : y ∈ U)
    (_hr : 0 < radius f (d i) (d j) U y) (hx : x ∈ U) :
    ¬ (0 < d i x y ∧ d i x y < radius f (d i) (d j) U y) := by
  intro h
  exact h.1.ne' (positive_colip_entry_reflects_zero d f U K i j hK hpos x hx y hy
    (radius_zero hx h.2))

theorem uniform_gap [Fintype I] {K : I → I → ℝ≥0∞}
    (hK : IsCoLipMatrix d f U K) (hpos : 0 < K i j)
    (_hr : 0 < nullMatrix d f U j i) (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ nullMatrix d f U j i ≤ d i x y := by
  by_cases h : nullMatrix d f U j i ≤ d i x y
  · exact Or.inr h
  · exact Or.inl (positive_colip_entry_reflects_zero d f U K i j hK hpos x hx y hy
      (uniform_zero hK.2.1 hK.1 hx hy (lt_of_not_ge h)))

noncomputable def diameter (P : X → X → ℝ≥0∞) (A : Set X) : ℝ≥0∞ :=
  ⨆ x : A, ⨆ y : A, P x y

theorem le_diameter (hx : x ∈ A) (hy : y ∈ A) : P x y ≤ diameter P A :=
  le_iSup_of_le ⟨x,hx⟩ (le_iSup_of_le ⟨y,hy⟩ le_rfl)

structure ScaleFamily (X I : Type) where
  scale : I → {A : Set X // A.Nonempty} → ℝ≥0∞
  monotone : ∀ i A B, A.val ⊆ B.val → scale i A ≤ scale i B

noncomputable def diameterScale (d : I → X → X → ℝ≥0∞) : ScaleFamily X I where
  scale i A := diameter (d i) A.1
  monotone _i A _B h := iSup_le fun x : A.1 => iSup_le fun y : A.1 =>
    le_diameter (h x.2) (h y.2)

noncomputable def thresholdType (σ : ScaleFamily X I) (d : I → X → X → ℝ≥0∞)
    (f : Operator X bot) (A : Set X) (hn : A.Nonempty) (s t : ℝ≥0∞) (i j : I) :
    Bool × Bool := (decide (σ.scale i ⟨A,hn⟩ < s), decide (t ≤ nullMatrix d f A j i))

theorem threshold_four (σ : ScaleFamily X I) (_hA : A ⊆ dom f) (hn : A.Nonempty)
    {s t : ℝ≥0∞} (_hs : FinitePositive s) (_ht : FinitePositive t) :
    let q := thresholdType σ d f A hn s t i j
    let a := σ.scale i ⟨A,hn⟩
    let n := nullMatrix d f A j i
    ((q = (true,true) ↔ a < s ∧ t ≤ n) ∧
     (q = (true,false) ↔ a < s ∧ n < t) ∧
     (q = (false,true) ↔ s ≤ a ∧ t ≤ n) ∧
     (q = (false,false) ↔ s ≤ a ∧ n < t)) ∧
    (q = (true,true) ∨ q = (true,false) ∨ q = (false,true) ∨ q = (false,false)) := by
  dsimp
  constructor
  · simp [thresholdType, not_le, not_lt]
  · rcases thresholdType σ d f A hn s t i j with ⟨a,b⟩
    cases a <;> cases b <;> simp

theorem threshold_scale_mono (σ : ScaleFamily X I) (hn : A.Nonempty)
    {s s' t : ℝ≥0∞} (h : s ≤ s') :
    {p : I × I | (thresholdType σ d f A hn s t p.1 p.2).1 = true} ⊆
      {p : I × I | (thresholdType σ d f A hn s' t p.1 p.2).1 = true} := by
  intro p hp
  simp only [Set.mem_setOf_eq, thresholdType, decide_eq_true_eq] at hp ⊢
  exact hp.trans_le h

theorem threshold_null_antitone (σ : ScaleFamily X I) (hn : A.Nonempty)
    {s t t' : ℝ≥0∞} (h : t ≤ t') :
    {p : I × I | (thresholdType σ d f A hn s t' p.1 p.2).2 = true} ⊆
      {p : I × I | (thresholdType σ d f A hn s t p.1 p.2).2 = true} := by
  intro p hp
  simp only [Set.mem_setOf_eq, thresholdType, decide_eq_true_eq] at hp ⊢
  exact h.trans hp

theorem scale_restrict (σ : ScaleFamily X I) (hn : A.Nonempty) (hb : B.Nonempty)
    (hBA : B ⊆ A) (_hA : A ⊆ dom f) {s : ℝ≥0∞} :
    σ.scale i ⟨B,hb⟩ ≤ σ.scale i ⟨A,hn⟩ ∧
    (σ.scale i ⟨A,hn⟩ < s → σ.scale i ⟨B,hb⟩ < s) :=
  ⟨σ.monotone i _ _ hBA, fun h => (σ.monotone i _ _ hBA).trans_lt h⟩

theorem small_iff (hA : A ⊆ dom f) (hn : A.Nonempty)
    {s t : ℝ≥0∞} (_hs : FinitePositive s) (_ht : FinitePositive t)
    (hdiam : diameter P A < s) (hst : s ≤ t) :
    t ≤ uniform f P Q A A ↔ ∀ x ∈ A, ∀ y ∈ A, Q (f.func x) (f.func y) = 0 := by
  constructor
  · intro h x hx y hy
    exact uniform_zero hA hn hx hy ((le_diameter hx hy).trans_lt (hdiam.trans_le (hst.trans h)))
  · exact fun h => le_uniform_iff.mpr fun y hy x hx _ => h x hx y hy

end Chapter
