import Components
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

variable {U : Set X} {f g : X → X} {d : I → D X}
def eqRel (U : Set X) (f : X → X) : Set (U × U) := {a | f a.1 = f a.2}
def zeroRel (d : I → D X) (U : Set X) (f : X → X) : Set (U × U) :=
  {a | GaugeZeroRelated d (f a.1) (f a.2)}
def finer (d : I → D X) (U : Set X) (f g : X → X) := zeroRel d U f ⊆ zeroRel d U g

theorem zeroRel_fiber (hd : ∀ i, ExtendedPseudoMetric X b (d i)) (x y : U) :
    (x,y) ∈ zeroRel d U f ↔ (y : X) ∈ fiber (subD d univ) f U (f x) := by
  change (∀ i, d i (f x) (f y) = 0) ↔ _ ∧ _
  simp [y.property, sub_zero, fun i => (hd i).symm (f y) (f x)]

def img (U : Set X) (f : X → X) (x : U) : f '' U := ⟨_, x, x.property, rfl⟩
theorem img_onto : Function.Surjective (img U f) := by
  rintro ⟨_,x,hx,rfl⟩
  exact ⟨⟨x,hx⟩,rfl⟩

theorem factor_iff {A B C : Type} (a : A → B) (ha : Function.Surjective a) (c : A → C) :
    (∃ T : B → C, ∀ x, T (a x) = c x) ↔ ∀ x y, a x = a y → c x = c y := by
  constructor
  · rintro ⟨T,hT⟩ x y h
    rw [← hT x, ← hT y,h]
  · intro h
    exact ⟨fun y => c ((ha y).choose), fun x => h _ _ (ha (a x)).choose_spec⟩

def Factor (U : Set X) (f g : X → X) :=
  ∃ T : f '' U → X, ∀ x : U, T (img U f x) = g x

theorem point_iff : Factor U f g ↔ eqRel U f ⊆ eqRel U g := by
  unfold Factor
  rw [factor_iff _ img_onto]
  exact ⟨fun h a ha => h a.1 a.2 (Subtype.ext ha),
    fun h x y he => h (show (x,y) ∈ eqRel U f from congrArg Subtype.val he)⟩

theorem point_both : Factor U f g ∧ Factor U g f ↔ eqRel U f = eqRel U g := by
  rw [point_iff,point_iff,Set.Subset.antisymm_iff]

def PosFin (r : ENNReal) := 0 < r ∧ r < ⊤

theorem factor_lip {p : D X} {K L : ENNReal} (hk : PosFin K) (_hl : L < ⊤)
    (T : f '' U → X) (ht : ∀ x : U, T (img U f x) = g x)
    (lo : ∀ x ∈ U, ∀ y ∈ U, K * p x y ≤ p (f x) (f y))
    (hi : ∀ x ∈ U, ∀ y ∈ U, p (g x) (g y) ≤ L * p x y) (u v : f '' U) :
    p (T u) (T v) ≤ (L / K) * p u v := by
  obtain ⟨x,rfl⟩ := img_onto u
  obtain ⟨y,rfl⟩ := img_onto v
  rw [ht,ht]
  calc
    _ ≤ L * p x y := hi x x.2 y y.2
    _ = (L / K) * (K * p x y) := by
      rw [← mul_assoc, ENNReal.div_mul_cancel hk.1.ne' hk.2.ne]
    _ ≤ _ := mul_le_mul_right (lo x x.2 y y.2) _

variable (hd : ∀ i, ExtendedPseudoMetric X b (d i))
def imageSetoid (f : X → X) (U : Set X) : Setoid (f '' U) where
  r x y := GaugeZeroRelated d x.val y.val
  iseqv := (gauge_zero_related_equivalence d (fun i => (hd i).dist_self)
    (fun i => (hd i).symm) (fun i => (hd i).triangle)).comap Subtype.val

def cls (f : X → X) (U : Set X) (x : U) := Quotient.mk (imageSetoid hd f U) (img U f x)

theorem cls_onto : Function.Surjective (cls hd f U) := by
  intro q
  induction q using Quotient.inductionOn with
  | _ u => obtain ⟨x,rfl⟩ := img_onto u; exact ⟨x,rfl⟩

theorem cls_eq {x y : U} : cls hd f U x = cls hd f U y ↔ (x,y) ∈ zeroRel d U f :=
  Quotient.eq

def QFactor (f g : X → X) (U : Set X) :=
  ∃ T : Quotient (imageSetoid hd f U) → Quotient (imageSetoid hd g U),
    ∀ x : U, T (cls hd f U x) = cls hd g U x

theorem quotient_iff : QFactor hd f g U ↔ finer d U f g := by
  unfold QFactor
  rw [factor_iff _ (cls_onto hd)]
  simp only [cls_eq]
  exact ⟨fun h a => h a.1 a.2, fun h x y => @h (x,y)⟩

theorem quotient_both : QFactor hd f g U ∧ QFactor hd g f U ↔
    zeroRel d U f = zeroRel d U g := by
  rw [quotient_iff,quotient_iff,Set.Subset.antisymm_iff]
  rfl

include hd in
theorem separated (hs : ∀ u ∈ f '' U, ∀ v ∈ f '' U, GaugeZeroRelated d u v → u = v) :
    eqRel U f = zeroRel d U f := by
  ext a
  constructor
  · intro h i
    change f a.1 = f a.2 at h
    rw [h,(hd i).dist_self]
  · exact hs _ (img U f a.1).2 _ (img U f a.2).2

theorem separated_criteria
    (hf : ∀ u ∈ f '' U, ∀ v ∈ f '' U, GaugeZeroRelated d u v → u = v)
    (hg : ∀ u ∈ g '' U, ∀ v ∈ g '' U, GaugeZeroRelated d u v → u = v) :
    (Factor U f g ↔ QFactor hd f g U) ∧
    ((Factor U f g ∧ Factor U g f) ↔ (QFactor hd f g U ∧ QFactor hd g f U)) := by
  simp only [point_iff, quotient_iff, finer, separated hd hf, separated hd hg, iff_self, and_self]

theorem finer_preorder : (∀ f, finer d U f f) ∧
    (∀ f g k, finer d U f g → finer d U g k → finer d U f k) :=
  ⟨fun _ => Subset.rfl, fun _ _ _ h h' => h.trans h'⟩

theorem finer_chain {n : ℕ} {F : Fin (n+1) → X → X}
    (hs : ∀ k : Fin n, finer d U (F k.castSucc) (F k.succ)) :
    Monotone (fun k => zeroRel d U (F k)) := Fin.monotone_iff_le_succ.mpr hs

theorem finer_strict {n : ℕ} {F : Fin (n+1) → X → X}
    (hs : ∀ k : Fin n, finer d U (F k.castSucc) (F k.succ)) (r : Fin n)
    (hr : zeroRel d U (F r.castSucc) ⊂ zeroRel d U (F r.succ)) :
    zeroRel d U (F 0) ⊂ zeroRel d U (F (Fin.last n)) ∧
    ∃ a ∈ zeroRel d U (F (Fin.last n)), a ∉ zeroRel d U (F 0) := by
  have H := finer_chain hs
  obtain ⟨a,ha,hb⟩ := Set.exists_of_ssubset hr
  have hx := H (Fin.le_last r.succ) ha
  have hn : a ∉ zeroRel d U (F 0) := fun hh => hb (H (Fin.zero_le _) hh)
  exact ⟨⟨H (Fin.zero_le _),fun h => hn (h hx)⟩,a,hx,hn⟩

end
end C3
