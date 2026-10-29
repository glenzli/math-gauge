import Mathlib.Topology.Compactness.CompactlyGeneratedSpace
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.Topology.Category.TopCat.Yoneda

/-! Concrete compact generation and its mapping-space exponential law.
All probe carriers and all resulting carriers stay in universe `u`.
-/
noncomputable section
open TopologicalSpace Topology Set CategoryTheory
universe u
namespace MathGauge.Mapping

/-- The same carrier with the topology detected by compact Hausdorff probes. -/
def Kify (X : Type u) := X

instance (X : Type u) [TopologicalSpace X] : TopologicalSpace (Kify X) :=
  TopologicalSpace.compactlyGenerated.{u} X

def kdown {X : Type u} : Kify X → X := id
def kup {X : Type u} : X → Kify X := id

theorem continuous_kdown (X : Type u) [TopologicalSpace X] :
    Continuous (kdown : Kify X → X) := by
  exact continuous_from_compactlyGenerated (X := X) (Y := X) id (fun S g => g.continuous)

theorem continuous_kprobe {X : Type u} [TopologicalSpace X]
    (S : CompHaus.{u}) (f : C(S, X)) :
    Continuous (fun x : S => kup (f x)) := by
  let ev : (Σ (i : (T : CompHaus.{u}) × C(T, X)), i.fst) → X :=
    fun ⟨⟨_, g⟩, s⟩ => g s
  have h : ∀ (i : (T : CompHaus.{u}) × C(T, X)),
      Continuous[inferInstance, TopologicalSpace.compactlyGenerated.{u} X]
        (fun (a : i.fst) => ev ⟨i,a⟩) := by
    rw [← @continuous_sigma_iff]
    exact continuous_coinduced_rng
  exact h ⟨S,f⟩

theorem continuous_from_kify {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Kify X → Y)
    (h : ∀ (S : CompHaus.{u}) (g : C(S, X)), Continuous (fun x => f (kup (g x)))) :
    Continuous f :=
  continuous_from_compactlyGenerated (X := X) (fun x : X => f (kup x)) h

instance (X : Type u) [TopologicalSpace X] : UCompactlyGeneratedSpace.{u} (Kify X) := by
  apply uCompactlyGeneratedSpace_of_continuous_maps
  intro Y _ f hf
  exact continuous_from_compactlyGenerated (X := X) (fun x : X => f (kup x)) fun S g =>
    hf S ⟨fun x => kup (g x), continuous_kprobe S g⟩

theorem continuous_into_kify {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [UCompactlyGeneratedSpace.{u} X] {f : X → Y} (hf : Continuous f) :
    Continuous (fun x => kup (f x)) := by
  apply continuous_from_uCompactlyGeneratedSpace
  intro S g
  exact continuous_kprobe S ⟨f ∘ g, hf.comp g.continuous⟩

def kmap {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X,Y)) :
    C(Kify X, Kify Y) :=
  ⟨fun x => kup (f (kdown x)), continuous_into_kify (f.continuous.comp (continuous_kdown X))⟩

@[simp] theorem kmap_apply {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X,Y)) (x : Kify X) : kmap f x = kup (f (kdown x)) := rfl

@[simp] theorem kmap_id (X : Type u) [TopologicalSpace X] :
    kmap (ContinuousMap.id X) = ContinuousMap.id (Kify X) := rfl

@[simp] theorem kmap_comp {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X,Y)) (g : C(Y,Z)) :
    kmap (g.comp f) = (kmap g).comp (kmap f) := rfl

def kify_homeo (X : Type u) [TopologicalSpace X] [UCompactlyGeneratedSpace.{u} X] :
    Kify X ≃ₜ X where
  toFun := kdown
  invFun := kup
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_kdown X
  continuous_invFun := continuous_into_kify continuous_id

instance (X : Type u) [TopologicalSpace X] [T2Space X] : T2Space (Kify X) :=
  @T2Space.of_injective_continuous (Kify X) X _ _ _ kdown
    (fun _ _ h => h) (continuous_kdown X)

def kprod (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] := Kify (X × Y)

instance (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    TopologicalSpace (kprod X Y) := inferInstanceAs (TopologicalSpace (Kify (X × Y)))

instance (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    UCompactlyGeneratedSpace.{u} (kprod X Y) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{u} (Kify (X × Y)))

def kpair {W X Y : Type u} [TopologicalSpace W] [TopologicalSpace X] [TopologicalSpace Y]
    [UCompactlyGeneratedSpace.{u} W] (f : C(W,X)) (g : C(W,Y)) : C(W,kprod X Y) :=
  ⟨fun w => kup (f w, g w), continuous_into_kify (f.continuous.prodMk g.continuous)⟩

def kfst (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] : C(kprod X Y, X) :=
  ⟨fun p => (kdown p).1, continuous_fst.comp (continuous_kdown (X × Y))⟩

def ksnd (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] : C(kprod X Y, Y) :=
  ⟨fun p => (kdown p).2, continuous_snd.comp (continuous_kdown (X × Y))⟩

/-- The actual universal property of the compactly generated product. -/
def kprod_equiv (W X Y : Type u) [TopologicalSpace W] [TopologicalSpace X]
    [TopologicalSpace Y] [UCompactlyGeneratedSpace.{u} W] :
    C(W,kprod X Y) ≃ C(W,X) × C(W,Y) where
  toFun f := ⟨(kfst X Y).comp f, (ksnd X Y).comp f⟩
  invFun fg := kpair fg.1 fg.2
  left_inv f := by ext w; rfl
  right_inv fg := by cases fg; rfl

/-- Ordinary products before and after refinement have the same compact probes. -/
def kify_product_homeo (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    Kify (X × Y) ≃ₜ kprod (Kify X) (Kify Y) where
  toFun p := kup (kup (kdown p).1, kup (kdown p).2)
  invFun p := kup (kdown (kdown p).1, kdown (kdown p).2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply continuous_from_kify
    intro S g
    apply continuous_into_kify
    exact (continuous_kprobe S ⟨fun s => (g s).1,
      continuous_fst.comp g.continuous⟩).prodMk
      (continuous_kprobe S ⟨fun s => (g s).2, continuous_snd.comp g.continuous⟩)
  continuous_invFun := by
    apply continuous_into_kify
    exact ((continuous_kdown X).comp (kfst (Kify X) (Kify Y)).continuous).prodMk
      ((continuous_kdown Y).comp (ksnd (Kify X) (Kify Y)).continuous)

end MathGauge.Mapping
