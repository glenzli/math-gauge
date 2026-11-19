import Ch3.Factor

namespace MG
open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
variable {X I : Type} {b : X} {f g : Op b} {U A B : Set X} {p q s : Dist X}
variable {x y : X} {r t : ENNReal}

def legal (p q : Dist X) (f : Op b) (U : Set X) (y : X) : Set ENNReal :=
  {r | positiveFinite r ∧ ∀ x ∈ U, p x y < r → q (f.func x) (f.func y) = 0}
def radius (p q : Dist X) (f : Op b) (U : Set X) (y : X) := sSup (legal p q f U y)
def uniform (p q : Dist X) (f : Op b) (A U : Set X) := ⨅ y : A, radius p q f U y
def matrix (d : I → Dist X) (f : Op b) (U : Set X) (j i : I) := uniform (d i) (d j) f U U

theorem legalBall : r ∈ legal p q f U y ↔ positiveFinite r ∧
    ball p y r ∩ U ⊆ fiber q f U (f.func y) :=
  ⟨fun h => ⟨h.1,fun _ hx => ⟨hx.2,h.2 _ hx.2 hx.1⟩⟩,
   fun h => ⟨h.1,fun _ hx hd => (h.2 ⟨hd,hx⟩).2⟩⟩
theorem radiusEmpty (h : legal p q f U y = ∅) : radius p q f U y = 0 := by simp [radius,h]
theorem uniform_le (hy : y ∈ A) : uniform p q f A U ≤ radius p q f U y :=
  iInf_le _ (⟨y,hy⟩ : A)

theorem extractRadius (h : t < radius p q f U y) : ∃ r ∈ legal p q f U y, t < r :=
  lt_sSup_iff.mp h
theorem cutPoint (hx : x ∈ U) (h : p x y < radius p q f U y) : q (f.func x) (f.func y) = 0 := by
  obtain ⟨r,hr,ht⟩ := extractRadius h
  exact hr.2 _ hx ht

theorem radiusBound : t ≤ radius p q f U y ↔ ∀ x ∈ U, p x y < t → q (f.func x) (f.func y) = 0 := by
  constructor
  · exact fun h x hx hd => cutPoint hx (hd.trans_le h)
  · intro h
    apply le_of_forall_lt
    intro a ha
    obtain ⟨r,har,hrt⟩ := exists_between ha
    exact har.trans_le (le_sSup (s := legal p q f U y)
      ⟨⟨(zero_le a).trans_lt har, hrt.trans_le le_top⟩,fun x hx hd => h x hx (hd.trans hrt)⟩)

theorem uniformBound : t ≤ uniform p q f A U ↔
    ∀ y ∈ A, ∀ x ∈ U, p x y < t → q (f.func x) (f.func y) = 0 := by
  simp only [uniform,le_iInf_iff,Subtype.forall,radiusBound]

theorem cutUniform (hx : x ∈ U) (hy : y ∈ A) (h : p x y < uniform p q f A U) :
    q (f.func x) (f.func y) = 0 := cutPoint hx (h.trans_le (uniform_le hy))

theorem cutFiber (mq : ExtendedPseudoMetric X b q) (h : x ∈ fiber q f U (f.func y)) :
    q (f.func y) (f.func x) = 0 := (mq.symm _ _).trans h.2

theorem cutSymm (mp : ExtendedPseudoMetric X b p) (mq : ExtendedPseudoMetric X b q)
    (hx : x ∈ U) (h : p y x < radius p q f U y) : q (f.func y) (f.func x) = 0 :=
  cutFiber (U := U) mq ⟨hx,cutPoint (p := p) hx (by rwa [mp.symm x y])⟩

theorem cutComp (mq : ExtendedPseudoMetric X b q) {V : Set X} (_hV : V ⊆ dom g)
    (_hx : x ∈ dom f) (_hy : y ∈ dom f) (_hfx : f.func x ∈ V) (_hfy : f.func y ∈ V)
    (h : f.func y ∈ fiber q g V (g.func (f.func x))) : q ((g*f).func x) ((g*f).func y) = 0 :=
  cutFiber (f := g) mq h

theorem constSub (d : I → Dist X) {J : Set I} (h : ∀ j ∈ J, Const (d j) f U) :
    Const (subdist d J) f U :=
  fun x hx y hy => (subzero d J).2 fun j hj => h j hj x hx y hy

theorem constSubFiber (d : I → Dist X) {J : Set I} (h : ∀ j ∈ J, Const (d j) f U) (hy : y ∈ U) :
    fiber (subdist d J) f U (f.func y) = U := by
  ext x
  exact ⟨fun hx => hx.1,fun hx => ⟨hx,constSub d h x hx y hy⟩⟩

theorem constRadii (p : Dist X) (h : Const q f U) :
    (∀ y ∈ U, radius p q f U y = ⊤) ∧ uniform p q f U U = ⊤ :=
  ⟨fun _ hy => top_unique (radiusBound.2 fun _ hx _ => h _ hx _ hy),
    top_unique (uniformBound.2 fun _ hy _ hx _ => h _ hx _ hy)⟩

theorem identBase (mp : ExtendedPseudoMetric X b p) (h : Ident p f U) (hy : y ∈ U) :
    fiber p f U (f.func y) = {x ∈ U | p x y = 0} := by
  ext x
  exact and_congr_right fun hx => by rw [identDist mp h hx hy]

theorem identRadius (mp : ExtendedPseudoMetric X b p) (hi : Ident p f U) (hy : y ∈ U)
    (hr : positiveFinite r) (h : ball p y r ∩ U ⊆ {x ∈ U | p x y = 0}) :
    r ≤ radius p p f U y ∧ 0 < r :=
  ⟨le_sSup (legalBall.2 ⟨hr,by rwa [identBase mp hi hy]⟩),hr.1⟩

theorem radiusInf (d : I → Dist X) (J : Set I) :
    radius p (subdist d J) f U y = ⨅ j : J, radius p (d j) f U y := by
  apply le_antisymm
  · apply le_iInf
    intro j
    exact radiusBound.2 fun x hx hd => (subzero d J).1 (cutPoint hx hd) _ j.2
  · exact radiusBound.2 fun x hx hd => (subzero d J).2 fun j hj =>
      cutPoint hx (hd.trans_le (iInf_le (fun k : J => radius p (d k) f U y) ⟨j,hj⟩))

theorem finiteMin [Finite I] {J : Set I} (hJ : J.Nonempty) (v : I → ENNReal) :
    ∃ j ∈ J, v j = ⨅ k : J, v k := by
  letI : Nonempty J := hJ.to_subtype
  obtain ⟨j,h⟩ := exists_eq_ciInf_of_finite (f := fun k : J => v k)
  exact ⟨j,j.2,h⟩

theorem uniformInf (d : I → Dist X) (J : Set I) (i : I) :
    uniform (d i) (subdist d J) f U U = ⨅ j : J, matrix d f U j i := by
  simp only [uniform, radiusInf, matrix]
  exact iInf_comm

theorem uniformAnti (d : I → Dist X) {J K : Set I} (h : J ⊆ K) (i : I) :
    uniform (d i) (subdist d K) f U U ≤ uniform (d i) (subdist d J) f U U := by
  rw [uniformInf,uniformInf]
  exact le_iInf fun j => iInf_le (fun k : K => matrix d f U k i) ⟨j.val,h j.2⟩

theorem compZeroRadius (h : ∀ a ∈ f.func '' U, ∀ c ∈ f.func '' U,
    s a c = 0 → q (g.func a) (g.func c) = 0) :
    uniform p s f U U ≤ uniform p q (g*f) U U :=
  uniformBound.2 fun y hy x hx hd => h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ (cutUniform hx hy hd)

theorem compLipRadius {L : ENNReal} (_hL : positiveFinite L)
    (h : ∀ x ∈ U, ∀ y ∈ U, s (f.func x) (f.func y) ≤ L * p x y) :
    uniform s q g (f.func '' U) (f.func '' U) / L ≤ uniform p q (g*f) U U := by
  apply uniformBound.2
  intro y hy x hx hd
  apply cutUniform (f := g) (p := s) (mem_image_of_mem f.func hx) (mem_image_of_mem f.func hy)
  exact (h _ hx _ hy).trans_lt (by simpa [mul_comm] using ENNReal.mul_lt_of_lt_div hd)

theorem restrictRadius (h : B ⊆ A) : radius p q f A y ≤ radius p q f B y :=
  radiusBound.2 fun _ hx hd => cutPoint (h hx) hd

theorem restrictUniform (h : B ⊆ A) : uniform p q f A A ≤ uniform p q f B B :=
  uniformBound.2 fun _ hy _ hx hd => cutUniform (h hx) (h hy) hd

theorem separation (hx : x ∈ U) (hy : y ∈ U) (hp : 0 < q (f.func x) (f.func y)) :
    uniform p q f U U ≤ p x y := le_of_not_gt fun h => hp.ne' (cutUniform hx hy h)

theorem separationWitness {α τ : ENNReal} (_ht : positiveFinite τ) (_ha : positiveFinite α)
    (ha : uniform p q f U U < α) (_hat : α < τ) :
    ∃ x ∈ U, ∃ y ∈ U, ∃ ε, positiveFinite ε ∧ p x y < α ∧ ε ≤ q (f.func x) (f.func y) := by
  have hn := mt uniformBound.2 (not_le.mpr ha)
  push Not at hn
  obtain ⟨y,hy,x,hx,hd,hq⟩ := hn
  refine ⟨x,hx,y,hy,min 1 (q (f.func x) (f.func y)),⟨lt_min zero_lt_one (pos_iff_ne_zero.mpr hq),
    (min_le_left _ _).trans_lt ENNReal.one_lt_top⟩,hd,min_le_right _ _⟩

theorem thresholdBall (hr : t ≤ uniform p q f U U) (hy : y ∈ U) :
    ball p y t ∩ U ⊆ fiber q f U (f.func y) :=
  fun _ hx => ⟨hx.2,cutUniform hx.2 hy (lt_of_lt_of_le hx.1 hr)⟩

theorem pointGap [Fintype I] (d : I → Dist X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hk : 0 < K i j) (hy : y ∈ U)
    (_hr : 0 < radius (d i) (d j) f U y) (hx : x ∈ U) :
    d i x y ∉ Ioo 0 (radius (d i) (d j) f U y) :=
  fun h => h.1.ne' (positive_colip_entry_reflects_zero d f U K i j hK hk x hx y hy (cutPoint hx h.2))

theorem uniformGap [Fintype I] (d : I → Dist X) (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hk : 0 < K i j) (hy : y ∈ U)
    (_hr : 0 < matrix d f U j i) (hx : x ∈ U) : d i x y = 0 ∨ matrix d f U j i ≤ d i x y := by
  by_cases h : matrix d f U j i ≤ d i x y
  · exact Or.inr h
  · exact Or.inl (positive_colip_entry_reflects_zero d f U K i j hK hk x hx y hy
      (cutUniform hx hy (lt_of_not_ge h)))

end
end MG
