import Factors
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

def legal (p q : D X) (f : X → X) (U : Set X) (y : X) : Set ENNReal :=
  {r | PosFin r ∧ ∀ x ∈ U, p x y < r → q (f x) (f y) = 0}

def rad (p q : D X) (f : X → X) (U : Set X) (y : X) := sSup (legal p q f U y)
def uniform (p q : D X) (f : X → X) (A U : Set X) := ⨅ y : A, rad p q f U y
def N (d : I → D X) (f : X → X) (U : Set X) (j i : I) := uniform (d i) (d j) f U U

variable {p q s : D X} {f g : X → X} {U A B : Set X} {x y : X} {r L : ENNReal}
variable {d : I → D X} {J K : Set I}

theorem legal_ball : r ∈ legal p q f U y ↔
    PosFin r ∧ ball p y r ∩ U ⊆ fiber q f U (f y) :=
  ⟨fun h => ⟨h.1,fun x hx => ⟨hx.2,h.2 x hx.2 hx.1⟩⟩,
   fun h => ⟨h.1,fun _ hx hxy => (h.2 ⟨hxy,hx⟩).2⟩⟩

theorem below_rad (hx : x ∈ U) (hlt : p x y < rad p q f U y) : q (f x) (f y) = 0 := by
  obtain ⟨ρ,hρ,hlt'⟩ := lt_sSup_iff.mp hlt
  exact hρ.2 x hx hlt'

theorem le_rad : r ≤ rad p q f U y ↔ ∀ x ∈ U, p x y < r → q (f x) (f y) = 0 := by
  refine ⟨fun h _ hx hp => below_rad hx (hp.trans_le h), ?_⟩
  intro h
  by_contra! hr
  obtain ⟨t,ht,ht'⟩ := exists_between hr
  exact ht.not_ge (le_sSup (s := legal p q f U y) ⟨⟨(zero_le _).trans_lt ht,ht'.trans_le le_top⟩,
    fun x hx hp => h x hx (hp.trans ht')⟩)

theorem le_uniform : r ≤ uniform p q f A U ↔
    ∀ y ∈ A, ∀ x ∈ U, p x y < r → q (f x) (f y) = 0 := by
  simp [uniform, le_iInf_iff,le_rad]

theorem uniform_zero (hx : x ∈ U) (hy : y ∈ U) (h : p x y < uniform p q f U U) :
    q (f x) (f y) = 0 := le_uniform.mp le_rfl y hy x hx h

theorem positive_sep (hx : x ∈ U) (hy : y ∈ U) (h : 0 < q (f x) (f y)) :
    uniform p q f U U ≤ p x y := le_of_not_gt (fun hh => h.ne' (uniform_zero hx hy hh))

theorem uniform_witness (h : uniform p q f U U < r) :
    ∃ x ∈ U, ∃ y ∈ U, ∃ ε, PosFin ε ∧ p x y < r ∧ ε ≤ q (f x) (f y) := by
  have hn := mt le_uniform.mpr h.not_ge
  push Not at hn
  obtain ⟨y,hy,x,hx,hxy,hq⟩ := hn
  exact ⟨x,hx,y,hy,min 1 (q (f x) (f y)),⟨lt_min zero_lt_one (pos_iff_ne_zero.mpr hq),
    (min_le_left _ _).trans_lt ENNReal.one_lt_top⟩,hxy,min_le_right _ _⟩

theorem sub_const (hc : ∀ j ∈ J, Const (d j) f U) : Const (subD d J) f U :=
  fun x hx y hy => sub_zero.mpr fun j hj => hc j hj x hx y hy

theorem const_full (hc : Const q f U) (hy : y ∈ U) : fiber q f U (f y) = U :=
  Set.Subset.antisymm (fun _ h => h.1) (fun x hx => ⟨hx,hc x hx y hy⟩)

theorem const_top (hc : Const q f U) :
    (∀ y ∈ U, rad p q f U y = ⊤) ∧ uniform p q f U U = ⊤ :=
  ⟨fun y hy => top_unique (le_rad.mpr fun x hx _ => hc x hx y hy),
   top_unique (le_uniform.mpr fun y hy x hx _ => hc x hx y hy)⟩

theorem ident_base (hd : ExtendedPseudoMetric X b p) (hi : Ident p f U) (hy : y ∈ U) :
    fiber p f U (f y) = {x ∈ U | p x y = 0} := by
  ext x
  exact and_congr_right fun hx => by rw [ident_dist hd hi hx hy]

theorem ident_rad (hd : ExtendedPseudoMetric X b p) (hi : Ident p f U) (hy : y ∈ U)
    (hr : PosFin r) (hh : ball p y r ∩ U ⊆ {x ∈ U | p x y = 0}) :
    r ≤ rad p p f U y ∧ 0 < r :=
  ⟨le_sSup (legal_ball.mpr ⟨hr,by rwa [ident_base hd hi hy]⟩),hr.1⟩

theorem rad_sub : rad p (subD d J) f U y = ⨅ j : J, rad p (d j) f U y := by
  apply le_antisymm
  · exact le_iInf fun j => le_rad.mpr fun x hx hp => sub_zero.mp (below_rad hx hp) j j.2
  · apply le_rad.mpr
    intro x hx hp
    exact sub_zero.mpr fun j hj => below_rad hx (hp.trans_le (iInf_le _ (⟨j,hj⟩ : J)))

theorem uniform_sub (i : I) :
    uniform (d i) (subD d J) f U U = ⨅ j : J, N d f U j i := by
  unfold uniform N
  simp only [rad_sub]
  exact iInf_comm

theorem attained_min [Finite I] (hj : J.Nonempty) (a : J → ENNReal) :
    ∃ j, a j = ⨅ k, a k := by
  letI : Nonempty J := hj.to_subtype
  exact exists_eq_ciInf_of_finite

theorem uniform_sub_anti (h : J ⊆ K) (i : I) :
    uniform (d i) (subD d K) f U U ≤ uniform (d i) (subD d J) f U U := by
  rw [uniform_sub,uniform_sub]
  exact le_iInf fun j => iInf_le _ (⟨j.1,h j.2⟩ : K)

theorem fiber_cut (hd : ExtendedPseudoMetric X b q) (h : x ∈ fiber q f U (f y)) :
    q (f y) (f x) = 0 := (hd.symm _ _).trans h.2

theorem point_cut (hp : ExtendedPseudoMetric X b p) (hq : ExtendedPseudoMetric X b q)
    (hx : x ∈ U) (h : p y x < rad p q f U y) : q (f y) (f x) = 0 :=
  (hq.symm _ _).trans (below_rad hx ((hp.symm x y) ▸ h))

theorem comp_cut {F G : Op b} (hq : ExtendedPseudoMetric X b q)
    (_hx : x ∈ dom F) (_hy : y ∈ dom F) (_hU : U ⊆ dom G)
    (_hxU : F.func x ∈ U) (_hyU : F.func y ∈ U)
    (hh : F.func y ∈ fiber q G.func U (G.func (F.func x))) :
    q ((G * F).func x) ((G * F).func y) = 0 := fiber_cut (f := G.func) (x := F.func y) (y := F.func x) hq hh

theorem comp_zero (hh : ∀ u ∈ f '' U, ∀ v ∈ f '' U, q u v = 0 → s (g u) (g v) = 0) :
    uniform p q f U U ≤ uniform p s (g ∘ f) U U :=
  le_uniform.mpr fun y hy x hx hp => hh _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ (uniform_zero hx hy hp)

theorem scaled_lt (hL : PosFin L) {a e : ENNReal} : a < e / L ↔ L * a < e := by
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hL.1.ne') (Or.inl hL.2.ne), mul_comm]

theorem comp_lip (hL : PosFin L) (hl : ∀ x ∈ U, ∀ y ∈ U, q (f x) (f y) ≤ L * p x y) :
    uniform q s g (f '' U) (f '' U) / L ≤ uniform p s (g ∘ f) U U :=
  le_uniform.mpr fun y hy x hx hp => uniform_zero (p := q) (f := g) (x := f x) (y := f y) (mem_image_of_mem f hx) (mem_image_of_mem f hy)
    ((hl x hx y hy).trans_lt ((scaled_lt hL).mp hp))

theorem rad_restrict (h : B ⊆ A) : rad p q f A y ≤ rad p q f B y :=
  le_rad.mpr fun _ hx hp => below_rad (h hx) hp

theorem uniform_restrict (h : B ⊆ A) : uniform p q f A A ≤ uniform p q f B B :=
  le_uniform.mpr fun _ hy _ hx hp => uniform_zero (h hx) (h hy) hp

theorem threshold_ball (hr : r ≤ uniform p q f U U) (hy : y ∈ U) :
    ball p y r ∩ U ⊆ fiber q f U (f y) :=
  fun _ hx => ⟨hx.2,uniform_zero hx.2 hy (lt_of_lt_of_le hx.1 hr)⟩

def diameter (p : D X) (A : Set X) := ⨆ x : A, ⨆ y : A, p x y

theorem le_diameter (hx : x ∈ U) (hy : y ∈ U) : p x y ≤ diameter p U :=
  le_iSup_of_le (⟨x,hx⟩ : U) (le_iSup_of_le (⟨y,hy⟩ : U) le_rfl)

theorem diameter_le : diameter p U ≤ r ↔ ∀ x ∈ U, ∀ y ∈ U, p x y ≤ r := by
  simp [diameter,iSup_le_iff]

structure Scale (X I : Type) where
  val : I → {A : Set X // A.Nonempty} → ENNReal
  mono : ∀ i A B, A.val ⊆ B.val → val i A ≤ val i B

def diamScale (d : I → D X) : Scale X I :=
  ⟨fun i A => diameter (d i) A,fun _ _ _ h => diameter_le.mpr fun _ hx _ hy => le_diameter (h hx) (h hy)⟩

def bits (a n t u : ENNReal) : Bool × Bool := (decide (a < t),decide (u ≤ n))
def channel (σ : Scale X I) (A : {A : Set X // A.Nonempty}) (d : I → D X) (f : X → X)
    (t u : ENNReal) (i j : I) := bits (σ.val i A) (N d f A j i) t u

theorem bits_cases (a n t u : ENNReal) :
    (bits a n t u = (true,true) ↔ a < t ∧ u ≤ n) ∧
    (bits a n t u = (true,false) ↔ a < t ∧ n < u) ∧
    (bits a n t u = (false,true) ↔ t ≤ a ∧ u ≤ n) ∧
    (bits a n t u = (false,false) ↔ t ≤ a ∧ n < u) := by simp [bits]

theorem scale_threshold {a n t t' u : ENNReal} (h : t ≤ t') :
    (bits a n t u).1 = true → (bits a n t' u).1 = true := by simpa [bits] using (fun hh => lt_of_lt_of_le hh h : a < t → a < t')
theorem null_threshold {a n t u u' : ENNReal} (h : u ≤ u') :
    (bits a n t u').2 = true → (bits a n t u).2 = true := by simpa [bits] using (fun hh => h.trans hh : u' ≤ n → u ≤ n)

theorem scale_restrict (σ : Scale X I) (i : I) {A B} (h : B.val ⊆ A.val) (t : ENNReal) :
    σ.val i B ≤ σ.val i A ∧ (σ.val i A < t → σ.val i B < t) :=
  ⟨σ.mono i B A h, fun hh => (σ.mono i B A h).trans_lt hh⟩

theorem small_iff {t u : ENNReal} (h : diameter p U < t) (ht : t ≤ u) :
    u ≤ uniform p q f U U ↔ Const q f U :=
  ⟨fun hn _ hx _ hy => uniform_zero hx hy ((le_diameter hx hy).trans_lt (h.trans_le (ht.trans hn))),
   fun hc => (const_top (p := p) hc).2 ▸ le_top⟩

theorem point_gap [Fintype I] {F : Op b} {K : I → I → ENNReal} {i j : I}
    (hk : IsCoLipMatrix d F U K) (hp : 0 < K i j) (hx : x ∈ U) (hy : y ∈ U) :
    d i x y ∉ Ioo 0 (rad (d i) (d j) F.func U y) := by
  intro hh
  exact hh.1.ne' (positive_colip_entry_reflects_zero d F U K i j hk hp x hx y hy (below_rad hx hh.2))

theorem uniform_gap [Fintype I] {F : Op b} {K : I → I → ENNReal} {i j : I}
    (hk : IsCoLipMatrix d F U K) (hp : 0 < K i j) (hx : x ∈ U) (hy : y ∈ U) :
    d i x y = 0 ∨ N d F.func U j i ≤ d i x y := by
  by_cases hh : N d F.func U j i ≤ d i x y
  · exact Or.inr hh
  · exact Or.inl (positive_colip_entry_reflects_zero d F U K i j hk hp x hx y hy
      (uniform_zero hx hy (lt_of_not_ge hh)))

end
end C3
