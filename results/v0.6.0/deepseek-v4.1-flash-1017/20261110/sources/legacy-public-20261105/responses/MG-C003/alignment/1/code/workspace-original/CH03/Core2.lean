import CH03.Core1

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

variable {X : Type} {I : Type} {bot : X}

/-! ## Proposition 3.3 (abstract part) -/

theorem outer_const_composite_const
    (d : I → X → X → ENNReal) (φ ψ : Operator X bot) (U : Set X) (i : I)
    (hi : i ∈ Iconst d ψ (φ.func '' U)) :
    i ∈ Iconst d (ψ * φ) U := by
  intro x hx y hy
  exact hi (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩

/-! ## Corollary 3.4 -/

theorem inner_const_preserved_of_zero_row
    [Fintype I] (d : I → X → X → ENNReal) (φ ψ : Operator X bot)
    (U : Set X) (j : I) (L : I → I → ENNReal)
    (hj : j ∈ Iconst d φ U)
    (hL : IsLipMatrix d ψ (φ.func '' U) L)
    (hrow : ∀ k : I, k ≠ j → L k j = 0) :
    j ∈ Iconst d (ψ * φ) U := by
  intro x hx y hy
  have hx' : φ.func x ∈ φ.func '' U := ⟨x, hx, rfl⟩
  have hy' : φ.func y ∈ φ.func '' U := ⟨y, hy, rfl⟩
  have hbound' := hL.2 (φ.func x) hx' (φ.func y) hy' j
  have hsum : (∑ k : I, L k j * d k (φ.func x) (φ.func y)) =
      L j j * d j (φ.func x) (φ.func y) := by
    apply Finset.sum_eq_single j
    · intro k _ hk
      rw [hrow k hk, zero_mul]
    · intro hjmem
      exact (hjmem (Finset.mem_univ j)).elim
  have hconst : d j (φ.func x) (φ.func y) = 0 := hj x hx y hy
  rw [hsum] at hbound'
  have : d j ((ψ * φ).func x) ((ψ * φ).func y) ≤ 0 := by
    simpa [hconst] using hbound'
  exact le_antisymm this (zero_le _)

/-! ## Proposition 3.5 -/

theorem fiber_target_zero_eq
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (J : Set I) (U : Set X) {y y' : X}
    (hy : ∀ j ∈ J, d j y y' = 0) :
    Fiber d φ J y U = Fiber d φ J y' U := by
  ext x
  constructor
  · rintro ⟨hx, hxzero⟩
    refine ⟨hx, fun j hj => ?_⟩
    have hle : d j (φ.func x) y' ≤ 0 := by
      calc
        d j (φ.func x) y' ≤ d j (φ.func x) y + d j y y' := (hd j).triangle _ _ _
        _ = 0 := by rw [hxzero j hj, hy j hj]; simp
    exact le_antisymm hle (zero_le _)
  · rintro ⟨hx, hxzero⟩
    refine ⟨hx, fun j hj => ?_⟩
    have hyx : d j y' y = 0 := by
      rw [(hd j).symm]
      exact hy j hj
    have hle : d j (φ.func x) y ≤ 0 := by
      calc
        d j (φ.func x) y ≤ d j (φ.func x) y' + d j y' y := (hd j).triangle _ _ _
        _ = 0 := by rw [hxzero j hj, hyx]; simp
    exact le_antisymm hle (zero_le _)

theorem fiber_self_mem
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (J : Set I) (U : Set X) {x : X} (hx : x ∈ U) :
    x ∈ Fiber d φ J (φ.func x) U :=
  ⟨hx, fun j _ => hself j (φ.func x)⟩

theorem fiber_image_nonempty
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (J : Set I) (U : Set X) {y : X}
    (hy : y ∈ φ.func '' U) : (Fiber d φ J y U).Nonempty := by
  rcases hy with ⟨x, hx, rfl⟩
  exact ⟨x, fiber_self_mem d hself φ J U hx⟩

theorem fiber_cover
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (J : Set I) (U : Set X) :
    ∀ x : X, x ∈ U ↔ ∃ y : X, y ∈ φ.func '' U ∧ x ∈ Fiber d φ J y U := by
  intro x
  constructor
  · intro hx
    exact ⟨φ.func x, ⟨x, hx, rfl⟩, fiber_self_mem d hself φ J U hx⟩
  · rintro ⟨y, _, hx, _⟩
    exact hx

theorem fiber_eq_or_disjoint
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (J : Set I) (U : Set X) :
    ∀ y1 : X, y1 ∈ φ.func '' U → ∀ y2 : X, y2 ∈ φ.func '' U →
      Fiber d φ J y1 U = Fiber d φ J y2 U ∨
        Disjoint (Fiber d φ J y1 U) (Fiber d φ J y2 U) := by
  intro y1 hy1 y2 hy2
  by_cases hinter : (Fiber d φ J y1 U ∩ Fiber d φ J y2 U).Nonempty
  · left
    rcases hinter with ⟨x, hx1, hx2⟩
    have hzero : ∀ j ∈ J, d j y1 y2 = 0 := by
      intro j hj
      have hx1j : d j (φ.func x) y1 = 0 := hx1.2 j hj
      have hx2j : d j (φ.func x) y2 = 0 := hx2.2 j hj
      have hle : d j y1 y2 ≤ 0 := by
        calc
          d j y1 y2 ≤ d j y1 (φ.func x) + d j (φ.func x) y2 := (hd j).triangle _ _ _
          _ = 0 := by
            rw [← (hd j).symm, hx1j, hx2j]; simp
      exact le_antisymm hle (zero_le _)
    exact fiber_target_zero_eq d hd φ J U hzero
  · right
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hinter ⟨x, hx1, hx2⟩

/-- The de-duplicated image fibers form a partition of `U`. -/
theorem fiber_partition
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (J : Set I) (U : Set X) :
    (∀ x : X, x ∈ U ↔ ∃ y : X, y ∈ φ.func '' U ∧ x ∈ Fiber d φ J y U) ∧
    (∀ y1 : X, y1 ∈ φ.func '' U → ∀ y2 : X, y2 ∈ φ.func '' U →
      Fiber d φ J y1 U = Fiber d φ J y2 U ∨
        Disjoint (Fiber d φ J y1 U) (Fiber d φ J y2 U)) ∧
    (∀ y : X, y ∈ φ.func '' U → (Fiber d φ J y U).Nonempty) := by
  refine ⟨fiber_cover d (fun i x => (hd i).dist_self x) φ J U, ?_, ?_⟩
  · exact fiber_eq_or_disjoint d hd φ J U
  · intro y hy
    exact fiber_image_nonempty d (fun i x => (hd i).dist_self x) φ J U hy

theorem fiber_inter
    (d : I → X → X → ENNReal) (φ : Operator X bot) (J : Set I)
    (hJ : J.Nonempty) (U : Set X) (y : X) :
    Fiber d φ J y U = ⋂ j ∈ J, Fiber d φ ({j} : Set I) y U := by
  ext x
  constructor
  · rintro ⟨hx, hxzero⟩
    simp only [Set.mem_iInter]
    intro j hj
    exact ⟨hx, by simpa using hxzero j hj⟩
  · intro hx
    simp only [Set.mem_iInter] at hx
    rcases hJ with ⟨j0, hj0⟩
    have hx0 := hx j0 hj0
    refine ⟨hx0.1, ?_⟩
    intro j hj
    exact (hx j hj).2 j (by simp)

theorem fiber_antitone_subfamily
    (d : I → X → X → ENNReal) (φ : Operator X bot) {J K : Set I}
    (hJK : J ⊆ K) (U : Set X) (y : X) :
    Fiber d φ K y U ⊆ Fiber d φ J y U := by
  intro x hx
  exact ⟨hx.1, fun j hj => hx.2 j (hJK hj)⟩

theorem fiber_singleton_eq
    (d : I → X → X → ENNReal) (φ : Operator X bot) (i : I) (U : Set X) (y : X) :
    Fiber d φ ({i} : Set I) y U = {x | x ∈ U ∧ d i (φ.func x) y = 0} := by
  ext x
  simp [Fiber]

theorem fiber_full_subset_singleton
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (y : X) (i : I) :
    Fiber d φ (Set.univ : Set I) y U ⊆ Fiber d φ ({i} : Set I) y U :=
  fiber_antitone_subfamily d φ (by intro j _; simp) U y

theorem fiber_id_component
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (y : X) (hy : y ∈ U) (j : I)
    (hj : j ∈ Iid d φ U) :
    Fiber d φ ({j} : Set I) (φ.func y) U = {x | x ∈ U ∧ d j x y = 0} := by
  ext x
  constructor
  · rintro ⟨hx, hxzero⟩
    refine ⟨hx, ?_⟩
    have hiso := id_component_isometry d hd φ U j hj x hx y hy
    have hout : d j (φ.func x) (φ.func y) = 0 := by
      exact hxzero j (by simp)
    rwa [hiso] at hout
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, ?_⟩
    have hiso := id_component_isometry d hd φ U j hj x hx y hy
    intro k hk
    simp only [Set.mem_singleton_iff] at hk
    subst k
    rw [hiso, hxy]


theorem fiber_const_component_image
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (j : I)
    (hj : j ∈ Iconst d φ U) {y0 : X} (hy0 : y0 ∈ φ.func '' U) :
    Fiber d φ ({j} : Set I) y0 U = U := by
  rcases hy0 with ⟨z, hz, rfl⟩
  ext x
  constructor
  · intro hx; exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    intro k hk
    simp only [Set.mem_singleton_iff] at hk
    subst k
    exact hj x hx z hz

theorem fiber_const_component_empty
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (j : I)
    (hj : j ∈ Iconst d φ U) {y0 y : X}
    (hy0 : y0 ∈ φ.func '' U) (hpos : 0 < d j y y0) :
    Fiber d φ ({j} : Set I) y U = ∅ := by
  ext x
  constructor
  · intro hx
    exfalso
    have hxy : d j (φ.func x) y = 0 := hx.2 j (by simp)
    rcases hy0 with ⟨z, hz, rfl⟩
    have hxz : d j (φ.func x) (φ.func z) = 0 := hj x hx.1 z hz
    have hle : d j (φ.func z) y ≤ 0 := by
      calc
        d j (φ.func z) y ≤ d j (φ.func z) (φ.func x) + d j (φ.func x) y :=
          (hd j).triangle _ _ _
        _ = 0 := by rw [← (hd j).symm, hxz, hxy]; simp
    have hthis : d j (φ.func z) y = 0 := le_antisymm hle (zero_le _)
    rw [(hd j).symm] at hthis
    exact (ne_of_gt hpos) hthis
  · intro hx; simp at hx

/-! ## Proposition 3.6 (point-value factorization) -/

theorem point_factor_necessary
    (φA φB : Operator X bot) (U : Set X)
    (hT : PointFactorExists φA φB U) :
    REq φA U ⊆ REq φB U := by
  rcases hT with ⟨T, hT⟩
  intro p hp
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  have hsub : (⟨φA.func x, ⟨x, hx, rfl⟩⟩ : {z : X // z ∈ φA.func '' U}) =
      ⟨φA.func y, ⟨y, hy, rfl⟩⟩ := Subtype.ext hxy
  have h := congrArg T hsub
  simpa [hT x hx, hT y hy] using h

theorem point_factor_sufficient
    (φA φB : Operator X bot) (U : Set X)
    (h : REq φA U ⊆ REq φB U) :
    PointFactorExists φA φB U := by
  classical
  let rep : {y : X // y ∈ φA.func '' U} → X := fun y => Classical.choose y.2
  have hrepU : ∀ y, rep y ∈ U := fun y => (Classical.choose_spec y.2).1
  have hrepval : ∀ y, φA.func (rep y) = y.1 := fun y => (Classical.choose_spec y.2).2
  refine ⟨fun y => φB.func (rep y), ?_⟩
  intro x hx
  have hpair : (rep ⟨φA.func x, ⟨x, hx, rfl⟩⟩, x) ∈ REq φA U := by
    refine ⟨hrepU _, hx, ?_⟩
    rw [hrepval]
  exact (h hpair).2.2

theorem point_factor_iff
    (φA φB : Operator X bot) (U : Set X) :
    PointFactorExists φA φB U ↔ REq φA U ⊆ REq φB U :=
  ⟨point_factor_necessary φA φB U, point_factor_sufficient φA φB U⟩

theorem point_factor_both_iff
    (φA φB : Operator X bot) (U : Set X) :
    (PointFactorExists φA φB U ∧ PointFactorExists φB φA U) ↔
      REq φA U = REq φB U := by
  constructor
  · rintro ⟨hAB, hBA⟩
    exact le_antisymm (point_factor_necessary φA φB U hAB)
      (point_factor_necessary φB φA U hBA)
  · intro hEq
    constructor
    · exact point_factor_sufficient φA φB U (le_of_eq hEq)
    · exact point_factor_sufficient φB φA U (le_of_eq hEq.symm)

/-- Scalar Lip certificate on a single component. -/
def ScalarLip (d : X → X → ENNReal) (φ : Operator X bot) (U : Set X) (L : ENNReal) : Prop :=
  U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, d (φ.func x) (φ.func y) ≤ L * d x y

/-- Scalar co-Lip certificate on a single component. -/
def ScalarCoLip (d : X → X → ENNReal) (φ : Operator X bot) (U : Set X) (K : ENNReal) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, K * d x y ≤ d (φ.func x) (φ.func y)

theorem point_factor_scalar_lip
    (d : X → X → ENNReal) (φA φB : Operator X bot) (U : Set X)
    (T : {y : X // y ∈ φA.func '' U} → X)
    (hT : ∀ (x : X) (hx : x ∈ U),
      T ⟨φA.func x, ⟨x, hx, rfl⟩⟩ = φB.func x)
    (K L : ENNReal)
    (hK : ScalarCoLip d φA U K) (hL : ScalarLip d φB U L)
    (hKpos : 0 < K) (hKtop : K ≠ ⊤) :
    ∀ y : {y : X // y ∈ φA.func '' U}, ∀ y' : {y : X // y ∈ φA.func '' U},
      d (T y) (T y') ≤ (L / K) * d y.1 y'.1 := by
  classical
  let rep : {y : X // y ∈ φA.func '' U} → X := fun y => Classical.choose y.2
  have hrepU : ∀ y, rep y ∈ U := fun y => (Classical.choose_spec y.2).1
  have hrepval : ∀ y, φA.func (rep y) = y.1 := fun y => (Classical.choose_spec y.2).2
  have hTy : ∀ y, T y = φB.func (rep y) := by
    intro y
    have hsub : (⟨φA.func (rep y), ⟨rep y, hrepU y, rfl⟩⟩ :
        {z : X // z ∈ φA.func '' U}) = y := Subtype.ext (hrepval y)
    calc
      T y = T ⟨φA.func (rep y), ⟨rep y, hrepU y, rfl⟩⟩ := congrArg T hsub.symm
      _ = φB.func (rep y) := hT (rep y) (hrepU y)
  intro y y'
  rw [hTy y, hTy y']
  have hco := hK.2.2 (rep y) (hrepU y) (rep y') (hrepU y')
  have hco' : K * d (rep y) (rep y') ≤ d y.1 y'.1 := by
    simpa [hrepval y, hrepval y'] using hco
  have hlip := hL.2 (rep y) (hrepU y) (rep y') (hrepU y')
  have hstep : d (rep y) (rep y') ≤ d y.1 y'.1 / K := by
    rw [ENNReal.le_div_iff_mul_le (Or.inl (ne_of_gt hKpos)) (Or.inl hKtop)]
    rwa [mul_comm]
  calc
    d (φB.func (rep y)) (φB.func (rep y'))
        ≤ L * d (rep y) (rep y') := hlip
    _ ≤ L * (d y.1 y'.1 / K) := by gcongr
    _ = (L / K) * d y.1 y'.1 := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      ac_rfl

/-! ## Proposition 3.7 (quotient factorization) -/

theorem quotient_factor_sufficient
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X)
    (h : RSim d φA U ⊆ RSim d φB U) :
    QuotientFactorExists d hd φA φB U := by
  classical
  let repA : {y : X // y ∈ φA.func '' U} → X := fun y => Classical.choose y.2
  have hrepAU : ∀ y, repA y ∈ U := fun y => (Classical.choose_spec y.2).1
  have hrepAval : ∀ y, φA.func (repA y) = y.1 := fun y => (Classical.choose_spec y.2).2
  let f : {y : X // y ∈ φA.func '' U} → ImageQuot d hd φB U :=
    fun y => imageQuotMk d hd φB U (repA y) (hrepAU y)
  have hf : ∀ p q : {y : X // y ∈ φA.func '' U},
      GaugeZeroRelated d p.1 q.1 → f p = f q := by
    intro p q hpq
    apply Quotient.sound
    have hA : GaugeZeroRelated d (φA.func (repA p)) (φA.func (repA q)) := by
      simpa [hrepAval] using hpq
    have hR : (repA p, repA q) ∈ RSim d φA U :=
      ⟨hrepAU p, hrepAU q, hA⟩
    exact (h hR).2.2
  let T : ImageQuot d hd φA U → ImageQuot d hd φB U := Quotient.lift f hf
  refine ⟨T, ?_⟩
  intro x hx
  change T (Quotient.mk _ ⟨φA.func x, ⟨x, hx, rfl⟩⟩) = imageQuotMk d hd φB U x hx
  change f ⟨φA.func x, ⟨x, hx, rfl⟩⟩ = imageQuotMk d hd φB U x hx
  apply Quotient.sound
  have hA : GaugeZeroRelated d (φA.func (repA ⟨φA.func x, ⟨x, hx, rfl⟩⟩))
      (φA.func x) := by
    have hval := hrepAval ⟨φA.func x, ⟨x, hx, rfl⟩⟩
    intro i
    rw [hval]
    exact (hd i).dist_self _
  have hR : (repA ⟨φA.func x, ⟨x, hx, rfl⟩⟩, x) ∈ RSim d φA U :=
    ⟨hrepAU _, hx, hA⟩
  exact (h hR).2.2

theorem quotient_factor_necessary
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X)
    (hT : QuotientFactorExists d hd φA φB U) :
    RSim d φA U ⊆ RSim d φB U := by
  rcases hT with ⟨T, hT⟩
  intro p hp
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  have hq : imageQuotMk d hd φA U x hx = imageQuotMk d hd φA U y hy :=
    Quotient.sound hxy
  have h := congrArg T hq
  rw [hT x hx, hT y hy] at h
  exact Quotient.exact h

theorem quotient_factor_iff
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X) :
    QuotientFactorExists d hd φA φB U ↔ RSim d φA U ⊆ RSim d φB U :=
  ⟨quotient_factor_necessary d hd φA φB U,
    quotient_factor_sufficient d hd φA φB U⟩

theorem quotient_factor_both_iff
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X) :
    (QuotientFactorExists d hd φA φB U ∧
      QuotientFactorExists d hd φB φA U) ↔
      RSim d φA U = RSim d φB U := by
  constructor
  · rintro ⟨hAB, hBA⟩
    exact le_antisymm (quotient_factor_necessary d hd φA φB U hAB)
      (quotient_factor_necessary d hd φB φA U hBA)
  · intro hEq
    exact ⟨quotient_factor_sufficient d hd φA φB U (le_of_eq hEq),
      quotient_factor_sufficient d hd φB φA U (le_of_eq hEq.symm)⟩

theorem req_subset_rsim
    (d : I → X → X → ENNReal) (hself : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (U : Set X) :
    REq φ U ⊆ RSim d φ U := by
  intro p hp
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  intro i
  rw [hxy]
  exact hself i (φ.func y)

theorem rsim_subset_req_of_separates
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (hsep : SeparatesOn d (φ.func '' U)) :
    RSim d φ U ⊆ REq φ U := by
  intro p hp
  rcases p with ⟨x, y⟩
  rcases hp with ⟨hx, hy, hzero⟩
  exact ⟨hx, hy, hsep (φ.func x) ⟨x, hx, rfl⟩ (φ.func y) ⟨y, hy, rfl⟩ hzero⟩

theorem quotient_point_factor_iff_of_separating
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X)
    (hsepA : SeparatesOn d (φA.func '' U))
    (hsepB : SeparatesOn d (φB.func '' U)) :
    QuotientFactorExists d hd φA φB U ↔ PointFactorExists φA φB U := by
  constructor
  · intro hq
    apply point_factor_sufficient
    intro p hp
    have hR : RSim d φA U ⊆ RSim d φB U :=
      (quotient_factor_iff d hd φA φB U).mp hq
    have hzA : GaugeZeroRelated d (φA.func p.1) (φA.func p.2) := by
      rw [hp.2.2]
      intro i; exact (hd i).dist_self _
    have hzB := hR ⟨hp.1, hp.2.1, hzA⟩
    exact ⟨hp.1, hp.2.1,
      hsepB (φB.func p.1) ⟨p.1, hp.1, rfl⟩ (φB.func p.2) ⟨p.2, hp.2.1, rfl⟩ hzB.2.2⟩
  · intro hp
    apply (quotient_factor_iff d hd φA φB U).mpr
    intro q hq
    have hEq : REq φA U ⊆ REq φB U := (point_factor_iff φA φB U).mp hp
    have hzA : GaugeZeroRelated d (φA.func q.1) (φA.func q.2) := hq.2.2
    have heqA := hsepA (φA.func q.1) ⟨q.1, hq.1, rfl⟩
      (φA.func q.2) ⟨q.2, hq.2.1, rfl⟩ hzA
    have hpA : (q.1, q.2) ∈ REq φA U := ⟨hq.1, hq.2.1, heqA⟩
    have heqB := hEq hpA
    refine ⟨hq.1, hq.2.1, ?_⟩
    intro i
    rw [heqB.2.2]
    exact (hd i).dist_self _

theorem quotient_point_factor_both_iff_of_separating
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φA φB : Operator X bot) (U : Set X)
    (hsepA : SeparatesOn d (φA.func '' U))
    (hsepB : SeparatesOn d (φB.func '' U)) :
    (QuotientFactorExists d hd φA φB U ∧
      QuotientFactorExists d hd φB φA U) ↔
    (PointFactorExists φA φB U ∧ PointFactorExists φB φA U) := by
  constructor
  · rintro ⟨hAB, hBA⟩
    exact ⟨(quotient_point_factor_iff_of_separating d hd φA φB U hsepA hsepB).mp hAB,
      (quotient_point_factor_iff_of_separating d hd φB φA U hsepB hsepA).mp hBA⟩
  · rintro ⟨hAB, hBA⟩
    exact ⟨(quotient_point_factor_iff_of_separating d hd φA φB U hsepA hsepB).mpr hAB,
      (quotient_point_factor_iff_of_separating d hd φB φA U hsepB hsepA).mpr hBA⟩

/-! ## Fiber preorder -/

theorem fiberPreorder_refl
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    FiberPreorder d φ φ U := fun _ h => h

theorem fiberPreorder_trans
    (d : I → X → X → ENNReal) {φA φB φC : Operator X bot} {U : Set X}
    (hAB : FiberPreorder d φA φB U) (hBC : FiberPreorder d φB φC U) :
    FiberPreorder d φA φC U := fun p hp => hBC (hAB hp)

theorem fiberPreorder_chain
    (d : I → X → X → ENNReal) (φ : ℕ → Operator X bot) (U : Set X) (m : ℕ)
    (hstep : ∀ r < m, FiberPreorder d (φ r) (φ (r + 1)) U) :
    ∀ a b : ℕ, a ≤ b → b ≤ m → FiberPreorder d (φ a) (φ b) U := by
  intro a b hab
  induction b with
  | zero =>
      intro hb
      have : a = 0 := Nat.eq_zero_of_le_zero hab
      subst a
      exact fun _ hp => hp
  | succ b ih =>
      intro hb
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · exact fun _ hp => hp
      · have hab' : a ≤ b := Nat.le_of_lt_succ hlt
        have hb' : b ≤ m := Nat.le_of_succ_le hb
        have hbm : b < m := Nat.lt_of_succ_le hb
        exact fiberPreorder_trans d (ih hab' hb') (hstep b hbm)

theorem fiberPreorder_chain_strict
    (d : I → X → X → ENNReal) (φ : ℕ → Operator X bot) (U : Set X) (m r : ℕ)
    (hstep : ∀ k < m, FiberPreorder d (φ k) (φ (k + 1)) U)
    (hr : r < m)
    (hstrict : ¬ RSim d (φ (r + 1)) U ⊆ RSim d (φ r) U) :
    RSim d (φ 0) U ⊆ RSim d (φ m) U ∧
      ¬ RSim d (φ m) U ⊆ RSim d (φ 0) U ∧
      ∃ p : X × X, p ∈ RSim d (φ m) U ∧ p ∉ RSim d (φ 0) U := by
  have h0m : FiberPreorder d (φ 0) (φ m) U :=
    fiberPreorder_chain d φ U m hstep 0 m (Nat.zero_le m) (Nat.le_refl m)
  have hr1m : FiberPreorder d (φ (r + 1)) (φ m) U :=
    fiberPreorder_chain d φ U m hstep (r + 1) m (Nat.succ_le_of_lt hr) (Nat.le_refl m)
  have h0r : FiberPreorder d (φ 0) (φ r) U :=
    fiberPreorder_chain d φ U m hstep 0 r (Nat.zero_le r) (Nat.le_of_lt hr)
  have hnot : ¬ RSim d (φ m) U ⊆ RSim d (φ 0) U := by
    intro hrev
    apply hstrict
    intro p hp
    exact h0r (hrev (hr1m hp))
  rcases Set.not_subset.mp hnot with ⟨p, hpm, hp0⟩
  exact ⟨h0m, hnot, p, hpm, hp0⟩

end formal_oet.vol_01.ch_03_operator_local_degeneracy
