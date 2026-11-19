import Chapter.Components
import formal_oet.vol_01.ch_01_foundations.metric_entropy

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {f g : Operator X bot} {U : Set X} {J K : Set I} {i : I}

def fiber (D : X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) (y : X) : Set X :=
  {x ∈ U | D (f.func x) y = 0}

theorem subfamily_zero (d : I → X → X → ℝ≥0∞) (J : Set I) (x y : X) :
    subfamily_pseudometric d J x y = 0 ↔ ∀ j ∈ J, d j x y = 0 := by
  constructor
  · intro h j hj
    exact nonpos_iff_eq_zero.mp (h ▸ le_iSup (fun k : J => d k.1 x y) ⟨j, hj⟩)
  · intro h
    exact nonpos_iff_eq_zero.mp (iSup_le fun j : J => (h j.1 j.2).le)

theorem subfamily_max [Finite I] (hJ : J.Nonempty) (x y : X) :
    ∃ j ∈ J, subfamily_pseudometric d J x y = d j x y := by
  haveI : Nonempty J := hJ.to_subtype
  obtain ⟨j, hj⟩ := Finite.exists_max (fun j : J => d j.1 x y)
  exact ⟨j, j.2, le_antisymm (iSup_le hj) (le_iSup (fun j : J => d j.1 x y) j)⟩

variable {D : X → X → ℝ≥0∞} {y z : X}

theorem fiber_target (_hU : U ⊆ dom f) (hD : ExtendedPseudoMetric X bot D)
    (h : D y z = 0) : fiber D f U y = fiber D f U z := by
  ext x
  have he : D (f.func x) y = D (f.func x) z := by
    rw [hD.symm (f.func x) y, zero_left hD h, hD.symm z]
  simp [fiber, he]

def fiberBlocks (D : X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) :
    Set (Set X) := (fun y => fiber D f U y) '' (f.func '' U)

theorem fiber_cover (_hU : U ⊆ dom f) (hD : ExtendedPseudoMetric X bot D) :
    (∀ B ∈ fiberBlocks D f U, B.Nonempty) ∧ ⋃₀ fiberBlocks D f U = U := by
  constructor
  · rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, hD.dist_self _⟩
  · ext x
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hx⟩
      exact hx.1
    · intro hx
      exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, hx, hD.dist_self _⟩

theorem fiber_eq_or_disjoint (hU : U ⊆ dom f) (hD : ExtendedPseudoMetric X bot D)
    (_hy : y ∈ f.func '' U) (_hz : z ∈ f.func '' U) :
    fiber D f U y = fiber D f U z ∨ Disjoint (fiber D f U y) (fiber D f U z) := by
  classical
  by_cases h : D y z = 0
  · exact Or.inl (fiber_target hU hD h)
  · right
    exact Set.disjoint_left.mpr fun x (hx : x ∈ fiber D f U y) (hx' : x ∈ fiber D f U z) =>
      h ((zero_left hD ((hD.symm y _).trans hx.2) z).trans hx'.2)

theorem fiber_partition (hU : U ⊆ dom f) (hD : ExtendedPseudoMetric X bot D) :
    (∀ B ∈ fiberBlocks D f U, B.Nonempty) ∧
    ⋃₀ fiberBlocks D f U = U ∧ (fiberBlocks D f U).PairwiseDisjoint id := by
  refine ⟨(fiber_cover hU hD).1, (fiber_cover hU hD).2, ?_⟩
  rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩ h
  exact (fiber_eq_or_disjoint hU hD hy hz).resolve_left h

theorem fiber_inter (_hU : U ⊆ dom f) (hJ : J.Nonempty) :
    fiber (subfamily_pseudometric d J) f U y = ⋂ j ∈ J, fiber (d j) f U y := by
  ext x
  simp only [fiber, Set.mem_iInter, Set.mem_setOf_eq, subfamily_zero]
  exact ⟨fun h j hj => ⟨h.1, h.2 j hj⟩, fun h =>
    ⟨(h hJ.choose hJ.choose_spec).1, fun j hj => (h j hj).2⟩⟩

theorem fiber_antitone (_hU : U ⊆ dom f) (_hJ : J.Nonempty) (hJK : J ⊆ K) :
    fiber (subfamily_pseudometric d K) f U y ⊆ fiber (subfamily_pseudometric d J) f U y :=
  fun _ hx => ⟨hx.1, (subfamily_zero _ _ _ _).mpr fun j hj =>
    (subfamily_zero _ _ _ _).mp hx.2 j (hJK hj)⟩

theorem fiber_singleton :
    fiber (subfamily_pseudometric d {i}) f U y = fiber (d i) f U y := by
  rw [subfamily_pseudometric_singleton]

theorem fiber_full (hU : U ⊆ dom f) :
    fiber (subfamily_pseudometric d Set.univ) f U y ⊆ fiber (d i) f U y := by
  rw [← fiber_singleton (d := d) (i := i)]
  exact fiber_antitone hU (Set.singleton_nonempty _) (Set.subset_univ _)

theorem fiber_ident (hd : ExtendedPseudoMetric X bot (d i)) (_hU : U ⊆ dom f)
    (hi : i ∈ Ident d f U) : fiber (d i) f U y = {x ∈ U | d i x y = 0} := by
  ext x
  constructor <;> intro h
  · exact ⟨h.1, (zero_left hd (hi.2 x h.1) y).symm.trans h.2⟩
  · exact ⟨h.1, (zero_left hd (hi.2 x h.1) y).trans h.2⟩

theorem fiber_const (hd : ExtendedPseudoMetric X bot (d i)) (_hU : U ⊆ dom f)
    (hc : i ∈ Const d f U) (hy : y ∈ f.func '' U) :
    fiber (d i) f U y = U ∧ (0 < d i z y → fiber (d i) f U z = ∅) := by
  obtain ⟨a, ha, rfl⟩ := hy
  have he : fiber (d i) f U (f.func a) = U :=
    Set.Subset.antisymm (fun _ h => h.1) (fun x hx => ⟨hx, hc x hx a ha⟩)
  refine ⟨he, fun hp => Set.eq_empty_iff_forall_notMem.mpr fun x hx => hp.ne' ?_⟩
  exact (zero_left hd ((hd.symm z _).trans hx.2) _).trans (hc x hx.1 a ha)

def pointPairs (f : Operator X bot) (U : Set X) : Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ f.func p.1 = f.func p.2}

def zeroPairs (d : I → X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) :
    Set (X × X) :=
  {p | p.1 ∈ U ∧ p.2 ∈ U ∧ GaugeZeroRelated d (f.func p.1) (f.func p.2)}

theorem zeroPairs_fiber (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    {x x' : X} (hx : x ∈ U) (hx' : x' ∈ U) :
    (x, x') ∈ zeroPairs d f U ↔ x' ∈ fiber (subfamily_pseudometric d Set.univ) f U (f.func x) := by
  constructor
  · intro h
    exact ⟨hx', (subfamily_zero _ _ _ _).mpr fun j _ =>
      ((hd j).symm _ _).trans (h.2.2 j)⟩
  · intro h
    exact ⟨hx, hx', fun j => ((hd j).symm _ _).trans
      ((subfamily_zero _ _ _ _).mp h.2 j (Set.mem_univ _))⟩

def imagePoint (f : Operator X bot) (U : Set X) (x : U) : f.func '' U :=
  ⟨f.func x, x, x.property, rfl⟩

def PointFactor (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : (f.func '' U : Set X) → X, ∀ x : U, T (imagePoint f U x) = g.func x

theorem point_factor_necessary (_hU : U ⊆ dom f ∩ dom g) (h : PointFactor f g U) :
    pointPairs f U ⊆ pointPairs g U := by
  obtain ⟨T, hT⟩ := h
  rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
  refine ⟨hx, hy, ?_⟩
  rw [← hT ⟨x,hx⟩, ← hT ⟨y,hy⟩]
  exact congrArg T (Subtype.ext hxy)

noncomputable def representative (f : Operator X bot) (U : Set X)
    (z : (f.func '' U : Set X)) : U :=
  ⟨z.property.choose, z.property.choose_spec.1⟩

theorem representative_spec (z : (f.func '' U : Set X)) :
    f.func (representative f U z) = z := z.property.choose_spec.2

theorem point_factor_sufficient (_hU : U ⊆ dom f ∩ dom g)
    (h : pointPairs f U ⊆ pointPairs g U) : PointFactor f g U := by
  refine ⟨fun z => g.func (representative f U z), fun x => ?_⟩
  let r := representative f U (imagePoint f U x)
  exact (h (show ((r : X), (x : X)) ∈ pointPairs f U from
    ⟨r.property, x.property, representative_spec _⟩)).2.2

theorem point_factor_both (hU : U ⊆ dom f ∩ dom g) :
    (PointFactor f g U ∧ PointFactor g f U) ↔ pointPairs f U = pointPairs g U := by
  have hU' : U ⊆ dom g ∩ dom f := fun _ hx => ⟨(hU hx).2, (hU hx).1⟩
  exact ⟨fun h => Set.Subset.antisymm (point_factor_necessary hU h.1)
    (point_factor_necessary hU' h.2),
    fun h => ⟨point_factor_sufficient hU h.le, point_factor_sufficient hU' h.ge⟩⟩

theorem point_factor_lip (_hU : U ⊆ dom f ∩ dom g)
    (T : (f.func '' U : Set X) → X) (hT : ∀ x : U, T (imagePoint f U x) = g.func x)
    {K L : ℝ≥0∞} (hK : 0 < K) (hKt : K < ⊤) (_hLt : L < ⊤)
    (hf : ∀ x ∈ U, ∀ y ∈ U, K * D x y ≤ D (f.func x) (f.func y))
    (hg : ∀ x ∈ U, ∀ y ∈ U, D (g.func x) (g.func y) ≤ L * D x y) :
    ∀ z z' : (f.func '' U : Set X), D (T z) (T z') ≤ L / K * D z z' := by
  rintro ⟨_,x,hx,rfl⟩ ⟨_,y,hy,rfl⟩
  change D (T (imagePoint f U ⟨x,hx⟩)) (T (imagePoint f U ⟨y,hy⟩)) ≤ _
  rw [hT, hT, div_eq_mul_inv, mul_assoc]
  refine (hg x hx y hy).trans (mul_le_mul_right ?_ L)
  rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hK.ne') (Or.inl hKt.ne)]
  simpa [mul_comm] using hf x hx y hy

def imageSetoid (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot)
    (U : Set X) : Setoid (f.func '' U : Set X) where
  r x y := GaugeZeroRelated d x y
  iseqv :=
    let h := gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
      (fun i => (hd i).symm) (fun i => (hd i).triangle)
    ⟨fun x => h.refl x, fun hxy => h.symm hxy, fun hxy hyz => h.trans hxy hyz⟩

def imageQuot (hd : ∀ i, ExtendedPseudoMetric X bot (d i)) (f : Operator X bot) (U : Set X) :=
  Quotient (imageSetoid hd f U)

def quotientPoint (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (U : Set X) (x : U) : imageQuot hd f U :=
  Quotient.mk _ (imagePoint f U x)

def QuotFactor (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (f g : Operator X bot) (U : Set X) : Prop :=
  ∃ T : imageQuot hd f U → imageQuot hd g U,
    ∀ x : U, T (quotientPoint hd f U x) = quotientPoint hd g U x

theorem quot_factor (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom f ∩ dom g) :
    QuotFactor hd f g U ↔ zeroPairs d f U ⊆ zeroPairs d g U := by
  constructor
  · rintro ⟨T,hT⟩ ⟨x,y⟩ ⟨hx,hy,hxy⟩
    refine ⟨hx,hy,?_⟩
    have eq : quotientPoint hd f U ⟨x,hx⟩ = quotientPoint hd f U ⟨y,hy⟩ :=
      Quotient.sound hxy
    exact @Quotient.exact _ (imageSetoid hd g U) (imagePoint g U ⟨x,hx⟩)
      (imagePoint g U ⟨y,hy⟩) ((hT _).symm.trans ((congrArg T eq).trans (hT _)))
  · intro h
    let T : (f.func '' U : Set X) → imageQuot hd g U :=
      fun z => quotientPoint hd g U (representative f U z)
    refine ⟨Quotient.lift T ?_, fun x => ?_⟩
    · intro z z' hzz
      apply Quotient.sound
      let r := representative f U z
      let s := representative f U z'
      apply (h (show ((r : X), (s : X)) ∈ zeroPairs d f U from
        ⟨r.property,s.property,?_⟩)).2.2
      simpa only [show f.func r = z from representative_spec z,
        show f.func s = z' from representative_spec z'] using hzz
    · apply Quotient.sound
      let r := representative f U (imagePoint f U x)
      apply (h (show ((r : X), (x : X)) ∈ zeroPairs d f U from
        ⟨r.property,x.property,?_⟩)).2.2
      intro i
      rw [show f.func r = f.func x from representative_spec (imagePoint f U x)]
      exact (hd i).dist_self _

theorem quot_factor_both (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f ∩ dom g) :
    (QuotFactor hd f g U ∧ QuotFactor hd g f U) ↔ zeroPairs d f U = zeroPairs d g U := by
  rw [quot_factor hd hU, quot_factor hd (f := g) (g := f)
    (fun _ hx => ⟨(hU hx).2, (hU hx).1⟩)]
  exact ⟨fun h => Set.Subset.antisymm h.1 h.2, fun h => ⟨h.le,h.ge⟩⟩

def SeparatesImage (d : I → X → X → ℝ≥0∞) (f : Operator X bot) (U : Set X) : Prop :=
  ∀ x ∈ f.func '' U, ∀ y ∈ f.func '' U, GaugeZeroRelated d x y → x = y

theorem pairs_of_separated (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (h : SeparatesImage d f U) : pointPairs f U = zeroPairs d f U := by
  apply Set.Subset.antisymm
  · rintro ⟨x,y⟩ ⟨hx,hy,he⟩
    exact ⟨hx,hy,fun i => he ▸ (hd i).dist_self _⟩
  · rintro ⟨x,y⟩ ⟨hx,hy,he⟩
    exact ⟨hx,hy,h _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ he⟩

theorem factor_of_separated (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f ∩ dom g) (hf : SeparatesImage d f U) (hg : SeparatesImage d g U) :
    (PointFactor f g U ↔ QuotFactor hd f g U) ∧
    ((PointFactor f g U ∧ PointFactor g f U) ↔
      (QuotFactor hd f g U ∧ QuotFactor hd g f U)) := by
  constructor
  · rw [quot_factor hd hU, ← pairs_of_separated hd hf, ← pairs_of_separated hd hg]
    exact ⟨point_factor_necessary hU, point_factor_sufficient hU⟩
  · rw [point_factor_both hU, quot_factor_both hd hU,
      pairs_of_separated hd hf, pairs_of_separated hd hg]

def FiberFiner (d : I → X → X → ℝ≥0∞) (U : Set X) (f g : Operator X bot) : Prop :=
  zeroPairs d f U ⊆ zeroPairs d g U

theorem fiber_preorder (d : I → X → X → ℝ≥0∞) (U : Set X) :
    Reflexive (FiberFiner (bot := bot) d U) ∧
    (∀ f g h : Operator X bot, FiberFiner d U f g → FiberFiner d U g h → FiberFiner d U f h) :=
  ⟨fun _ => Set.Subset.rfl, fun _ _ _ h h' => h.trans h'⟩

theorem fiber_finite_chain {m : ℕ} (fs : ℕ → Operator X bot)
    (_hU : ∀ k ≤ m, U ⊆ dom (fs k))
    (h : ∀ k < m, FiberFiner d U (fs k) (fs (k + 1))) {a b : ℕ}
    (hab : a ≤ b) (hb : b ≤ m) : FiberFiner d U (fs a) (fs b) := by
  induction b, hab using Nat.le_induction with
  | base => exact Set.Subset.rfl
  | succ k hak ih => exact (ih (by omega)).trans (h k (by omega))

theorem fiber_strict_chain {m : ℕ} (fs : ℕ → Operator X bot)
    (hU : ∀ k ≤ m, U ⊆ dom (fs k))
    (h : ∀ k < m, FiberFiner d U (fs k) (fs (k + 1))) {r : ℕ} (hr : r < m)
    (hs : zeroPairs d (fs r) U ⊂ zeroPairs d (fs (r+1)) U) :
    zeroPairs d (fs 0) U ⊂ zeroPairs d (fs m) U ∧
    (zeroPairs d (fs m) U \ zeroPairs d (fs 0) U).Nonempty := by
  obtain ⟨p,hp,hpn⟩ := Set.exists_of_ssubset hs
  have hmem := fiber_finite_chain fs hU h (a := r+1) (b := m) (by omega) le_rfl hp
  have hn : p ∉ zeroPairs d (fs 0) U := fun h0 =>
    hpn (fiber_finite_chain fs hU h (Nat.zero_le r) (by omega) h0)
  exact ⟨Set.ssubset_iff_subset_ne.mpr ⟨fiber_finite_chain fs hU h (Nat.zero_le m) le_rfl,
    fun eq => hn (eq ▸ hmem)⟩, p, hmem, hn⟩

end Chapter
