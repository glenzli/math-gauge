import Ch3.Components

namespace MG
open Set formal_oet.vol_01.ch_01_foundations
variable {X I : Type} {b : X} {f g k : Op b} {U : Set X} {d : I → Dist X}

def pairs (f : Op b) (U : Set X) (R : X → X → Prop) : Set (X × X) :=
  {z | z.1 ∈ U ∧ z.2 ∈ U ∧ R (f.func z.1) (f.func z.2)}
abbrev eqRel (f : Op b) (U : Set X) := pairs f U Eq
abbrev zeroRel (d : I → Dist X) (f : Op b) (U : Set X) := pairs f U (GaugeZeroRelated d)
def finer (d : I → Dist X) (U : Set X) (f g : Op b) := zeroRel d f U ⊆ zeroRel d g U

theorem relationFiber (m : ∀ i, ExtendedPseudoMetric X b (d i)) {x y : X} (hx : x ∈ U) (hy : y ∈ U) :
    (x,y) ∈ zeroRel d f U ↔ y ∈ fiber (subdist d univ) f U (f.func x) := by
  change (_ ∧ _ ∧ ∀ i, _ = 0) ↔ _ ∧ _ = 0
  simp [hx,hy,subzero, (m _).symm (f.func y) (f.func x)]

def atImage (f : Op b) (U : Set X) (x : U) : f.func '' U := ⟨_,x.val,x.property,rfl⟩
theorem ontoImage : Function.Surjective (atImage f U) := by
  rintro ⟨_,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

theorem descend {S A B : Type} (a : S → A) (v : S → B) (ha : Function.Surjective a) :
    (∃ t : A → B, ∀ x, t (a x) = v x) ↔ ∀ x y, a x = a y → v x = v y := by
  constructor
  · rintro ⟨t,h⟩ x y he
    rw [← h, ← h, he]
  · intro h
    exact ⟨fun z => v (ha z).choose, fun x => h _ _ (ha (a x)).choose_spec⟩

def transforms (f g : Op b) (U : Set X) :=
  ∃ t : (f.func '' U) → X, ∀ x : U, t (atImage f U x) = g.func x

theorem pointFactor : transforms f g U ↔ eqRel f U ⊆ eqRel g U := by
  unfold transforms
  rw [descend _ _ ontoImage]
  constructor
  · intro h z hz
    exact ⟨hz.1,hz.2.1,h ⟨_,hz.1⟩ ⟨_,hz.2.1⟩ (Subtype.ext hz.2.2)⟩
  · intro h x y he
    exact (h (show (x.val,y.val) ∈ eqRel f U from
      ⟨x.2,y.2,congrArg Subtype.val he⟩)).2.2

theorem bothPoint : transforms f g U ∧ transforms g f U ↔ eqRel f U = eqRel g U := by
  rw [pointFactor,pointFactor,Set.Subset.antisymm_iff]

def positiveFinite (r : ENNReal) := 0 < r ∧ r < ⊤

theorem factorLip {p : Dist X} {K L : ENNReal} (hK : positiveFinite K) (_hL : L < ⊤)
    (t : (f.func '' U) → X) (ht : ∀ x : U, t (atImage f U x) = g.func x)
    (lo : ∀ x ∈ U, ∀ y ∈ U, K * p x y ≤ p (f.func x) (f.func y))
    (hi : ∀ x ∈ U, ∀ y ∈ U, p (g.func x) (g.func y) ≤ L * p x y)
    (u v : f.func '' U) : p (t u) (t v) ≤ (L/K) * p u v := by
  obtain ⟨x,rfl⟩ := ontoImage u
  obtain ⟨y,rfl⟩ := ontoImage v
  rw [ht,ht]
  calc
    _ ≤ L * p x y := hi _ x.2 _ y.2
    _ = (L/K) * (K * p x y) := by rw [← mul_assoc, ENNReal.div_mul_cancel hK.1.ne' hK.2.ne]
    _ ≤ _ := mul_le_mul_right (lo _ x.2 _ y.2) _

def imageSetoid (m : ∀ i, ExtendedPseudoMetric X b (d i)) (f : Op b) (U : Set X) :
    Setoid (f.func '' U) where
  r x y := GaugeZeroRelated d x.val y.val
  iseqv := (gauge_zero_related_equivalence d (fun i => (m i).dist_self)
    (fun i => (m i).symm) (fun i => (m i).triangle)).comap Subtype.val

abbrev ImageQuot (m : ∀ i, ExtendedPseudoMetric X b (d i)) (f : Op b) (U : Set X) :=
  Quotient (imageSetoid m f U)
def atClass (m : ∀ i, ExtendedPseudoMetric X b (d i)) (f : Op b) (U : Set X) (x : U) :
    ImageQuot m f U := Quotient.mk _ (atImage f U x)

theorem classEq (m : ∀ i, ExtendedPseudoMetric X b (d i)) (x y : U) :
    atClass m f U x = atClass m f U y ↔ GaugeZeroRelated d (f.func x) (f.func y) :=
  Quotient.eq

theorem ontoClass (m : ∀ i, ExtendedPseudoMetric X b (d i)) : Function.Surjective (atClass m f U) := by
  intro q
  obtain ⟨s,rfl⟩ := Quotient.exists_rep q
  obtain ⟨x,rfl⟩ := ontoImage s
  exact ⟨x,rfl⟩

def quotTransforms (m : ∀ i, ExtendedPseudoMetric X b (d i)) (f g : Op b) (U : Set X) :=
  ∃ t : ImageQuot m f U → ImageQuot m g U, ∀ x : U, t (atClass m f U x) = atClass m g U x

theorem quotFactor (m : ∀ i, ExtendedPseudoMetric X b (d i)) : quotTransforms m f g U ↔ finer d U f g := by
  unfold quotTransforms
  rw [descend _ _ (ontoClass m)]
  simp only [classEq]
  constructor
  · intro h z hz
    exact ⟨hz.1,hz.2.1,h ⟨_,hz.1⟩ ⟨_,hz.2.1⟩ hz.2.2⟩
  · intro h x y he
    exact (h (show (x.val,y.val) ∈ zeroRel d f U from ⟨x.2,y.2,he⟩)).2.2

theorem bothQuot (m : ∀ i, ExtendedPseudoMetric X b (d i)) :
    quotTransforms m f g U ∧ quotTransforms m g f U ↔ zeroRel d f U = zeroRel d g U := by
  rw [quotFactor,quotFactor,Set.Subset.antisymm_iff]
  rfl

def separatesOn (d : I → Dist X) (S : Set X) :=
  ∀ x ∈ S, ∀ y ∈ S, GaugeZeroRelated d x y → x = y

theorem sepRel (m : ∀ i, ExtendedPseudoMetric X b (d i)) (hs : separatesOn d (f.func '' U)) :
    eqRel f U = zeroRel d f U := by
  apply Set.Subset.antisymm
  · intro z hz
    refine ⟨hz.1,hz.2.1,?_⟩
    intro i
    rw [hz.2.2, (m i).dist_self]
  · intro z hz
    exact ⟨hz.1,hz.2.1,hs _ (mem_image_of_mem _ hz.1) _ (mem_image_of_mem _ hz.2.1) hz.2.2⟩

theorem separatedFactors (m : ∀ i, ExtendedPseudoMetric X b (d i))
    (hf : separatesOn d (f.func '' U)) (hg : separatesOn d (g.func '' U)) :
    (transforms f g U ↔ quotTransforms m f g U) ∧
    ((transforms f g U ∧ transforms g f U) ↔ (quotTransforms m f g U ∧ quotTransforms m g f U)) := by
  rw [bothPoint,bothQuot,pointFactor,quotFactor,sepRel m hf,sepRel m hg]
  exact ⟨Iff.rfl,Iff.rfl⟩

theorem finerRefl : finer d U f f := Subset.rfl
theorem finerTrans (a : finer d U f g) (c : finer d U g k) : finer d U f k := a.trans c

theorem finerChain (F : ℕ → Op b) {n : ℕ} (step : ∀ r < n, finer d U (F r) (F (r+1)))
    {a c : ℕ} (hac : a ≤ c) (hc : c ≤ n) : finer d U (F a) (F c) := by
  induction c, hac using Nat.le_induction with
  | base => exact finerRefl
  | succ t _ ih => exact finerTrans (ih (by omega)) (step t (by omega))

theorem strictChain (F : ℕ → Op b) {n r : ℕ} (step : ∀ s < n, finer d U (F s) (F (s+1)))
    (hr : r < n) (hs : zeroRel d (F r) U ⊂ zeroRel d (F (r+1)) U) :
    zeroRel d (F 0) U ⊂ zeroRel d (F n) U ∧
      ∃ z ∈ zeroRel d (F (r+1)) U \ zeroRel d (F r) U, z ∈ zeroRel d (F n) U \ zeroRel d (F 0) U := by
  obtain ⟨z,hz,hn⟩ := Set.exists_of_ssubset hs
  have hz' := finerChain F step (a := r+1) (c := n) hr le_rfl hz
  have hn' : z ∉ zeroRel d (F 0) U := fun h => hn (finerChain F step (Nat.zero_le r) hr.le h)
  exact ⟨⟨finerChain F step (Nat.zero_le n) le_rfl, fun h => hn' (h hz')⟩,z,⟨hz,hn⟩,hz',hn'⟩

end MG
