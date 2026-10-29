import Kification

noncomputable section
open TopologicalSpace Topology Set CategoryTheory
universe u
namespace MathGauge.Mapping

variable {W A B : Type u} [TopologicalSpace W] [TopologicalSpace A] [TopologicalSpace B]

/-- The compact-open mapping space, with its compactly generated refinement. -/
def KMap (A B : Type u) [TopologicalSpace A] [TopologicalSpace B] := Kify C(A,B)

instance : TopologicalSpace (KMap A B) :=
  inferInstanceAs (TopologicalSpace (Kify C(A,B)))

instance : UCompactlyGeneratedSpace.{u} (KMap A B) :=
  inferInstanceAs (UCompactlyGeneratedSpace.{u} (Kify C(A,B)))

instance [T2Space B] : T2Space (KMap A B) :=
  inferInstanceAs (T2Space (Kify C(A,B)))

def kslice [UCompactlyGeneratedSpace.{u} A] (w : W) : C(A,kprod W A) :=
  kpair (ContinuousMap.const A w) (ContinuousMap.id A)

def kcurry_fun [UCompactlyGeneratedSpace.{u} A] (f : C(kprod W A,B)) : W → C(A,B) :=
  fun w => f.comp (kslice w)

theorem continuous_kcurry_co [UCompactlyGeneratedSpace.{u} W]
    [UCompactlyGeneratedSpace.{u} A] [T2Space A] (f : C(kprod W A,B)) :
    Continuous (kcurry_fun f) := by
  apply continuous_from_uCompactlyGeneratedSpace
  intro S g
  apply ContinuousMap.continuous_compactOpen.mpr
  intro C hC O hO
  letI : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let v : C(S × C, W × A) :=
    ⟨fun p => (g p.1, p.2.val), g.continuous.comp continuous_fst |>.prodMk
      (continuous_subtype_val.comp continuous_snd)⟩
  let vk : C(S × C, kprod W A) :=
    ⟨fun p => kup (v p), continuous_kprobe (CompHaus.of (S × C)) v⟩
  let fC : C(S × C,B) := f.comp vk
  have h := (ContinuousMap.isOpen_setOf_mapsTo (X := C) (Y := B) isCompact_univ hO).preimage
    fC.curry.continuous
  have heq : {s : S | MapsTo (fC.curry s) univ O} =
      {s : S | MapsTo ((kcurry_fun f) (g s)) C O} := by
    ext s
    simp only [mem_setOf_eq, MapsTo, mem_univ, forall_true_left, Subtype.forall]
    rfl
  exact heq ▸ h

def kcurry [UCompactlyGeneratedSpace.{u} W] [UCompactlyGeneratedSpace.{u} A]
    [T2Space A] (f : C(kprod W A,B)) : C(W,KMap A B) :=
  ⟨fun w => kup (kcurry_fun f w), continuous_into_kify (continuous_kcurry_co f)⟩

theorem continuous_kuncurry (g : C(W,KMap A B)) :
    Continuous (fun p : kprod W A => (kdown (g (kdown p).1)) (kdown p).2) := by
  apply continuous_from_kify
  intro S v
  let u : C(S,W) := ⟨fun s => (v s).1, continuous_fst.comp v.continuous⟩
  let b : C(S,A) := ⟨fun s => (v s).2, continuous_snd.comp v.continuous⟩
  have h : Continuous (fun s : S => (kdown (g (u s))).comp b) :=
    (ContinuousMap.continuous_precomp b).comp
      ((continuous_kdown C(A,B)).comp (g.continuous.comp u.continuous))
  exact continuous_eval.comp (h.prodMk continuous_id)

def kuncurry (g : C(W,KMap A B)) : C(kprod W A,B) :=
  ⟨fun p => (kdown (g (kdown p).1)) (kdown p).2, continuous_kuncurry g⟩

@[simp] theorem kcurry_apply [UCompactlyGeneratedSpace.{u} W]
    [UCompactlyGeneratedSpace.{u} A] [T2Space A]
    (f : C(kprod W A,B)) (w : W) (a : A) : kdown (kcurry f w) a = f (kup (w,a)) := rfl

@[simp] theorem kuncurry_apply (g : C(W,KMap A B)) (w : W) (a : A) :
    kuncurry g (kup (w,a)) = kdown (g w) a := rfl

/-- The full exponential law: no local compactness assumption on `A`. -/
def exponential_equiv [UCompactlyGeneratedSpace.{u} W]
    [UCompactlyGeneratedSpace.{u} A] [T2Space A] :
    C(W,KMap A B) ≃ C(kprod W A,B) where
  toFun := kuncurry
  invFun := kcurry
  left_inv g := by ext w a; rfl
  right_inv f := by ext p; rfl

def keval [UCompactlyGeneratedSpace.{u} A] [T2Space A] :
    C(kprod (KMap A B) A,B) := kuncurry (ContinuousMap.id _)

@[simp] theorem keval_apply [UCompactlyGeneratedSpace.{u} A] [T2Space A]
    (f : KMap A B) (a : A) : keval (kup (f,a)) = kdown f a := rfl

/-- The evaluation-induced map is exactly uncurrying, not an unrelated bijection. -/
theorem eval_exponential [UCompactlyGeneratedSpace.{u} W]
    [UCompactlyGeneratedSpace.{u} A] [T2Space A] (g : C(W,KMap A B)) :
    keval.comp (kpair (g.comp (kfst W A)) (ksnd W A)) = exponential_equiv g := by
  ext p
  rfl

end MathGauge.Mapping
