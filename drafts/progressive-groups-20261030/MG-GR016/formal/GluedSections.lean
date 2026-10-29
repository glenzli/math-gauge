import PrincipalGluing

noncomputable section
namespace MathGauge.GluedSections
open MathGauge.PrincipalGluing MathGauge.SplittingClassification
universe u v w
variable {R : Type u} [CommRing R]
variable {B : Type v} {C : Type w} [AddCommGroup B] [AddCommGroup C]
variable [Module R B] [Module R C]
variable {m : ℕ} (f : Fin m → R) (hf : Ideal.span (Set.range f)=⊤)

def glueValue (g : ∀ i,C →ₗ[R] Loc (f i) B)
    (hc : ∀ i j c,overlapLeft (f i) (f j) (g i c)=overlapRight (f i) (f j) (g j c)) (c : C) : B :=
  Classical.choose (element_gluing f hf (fun i => g i c) (fun i j => hc i j c))

theorem glueValue_spec (g : ∀ i,C →ₗ[R] Loc (f i) B)
    (hc : ∀ i j c,overlapLeft (f i) (f j) (g i c)=overlapRight (f i) (f j) (g j c)) (c : C) (i : Fin m) :
    loc (f i) (glueValue f hf g hc c)=g i c :=
  (Classical.choose_spec (element_gluing f hf (fun i => g i c) (fun i j => hc i j c))).1 i

def glueLinear (g : ∀ i,C →ₗ[R] Loc (f i) B)
    (hc : ∀ i j c,overlapLeft (f i) (f j) (g i c)=overlapRight (f i) (f j) (g j c)) : C →ₗ[R] B where
  toFun := glueValue f hf g hc
  map_add' c d := by
    apply cover_injective f hf
    intro i
    simp only [map_add,glueValue_spec]
  map_smul' r c := by
    apply cover_injective f hf
    intro i
    simp only [map_smul,glueValue_spec,RingHom.id_apply]

@[simp] theorem glueLinear_loc (g : ∀ i,C →ₗ[R] Loc (f i) B)
    (hc : ∀ i j c,overlapLeft (f i) (f j) (g i c)=overlapRight (f i) (f j) (g j c)) (c : C) (i : Fin m) :
    loc (f i) (glueLinear f hf g hc c)=g i c := glueValue_spec f hf g hc c i

theorem glueLinear_unique (g : ∀ i,C →ₗ[R] Loc (f i) B)
    (hc : ∀ i j c,overlapLeft (f i) (f j) (g i c)=overlapRight (f i) (f j) (g j c))
    (t : C →ₗ[R] B) (ht : ∀ i c,loc (f i) (t c)=g i c) : t=glueLinear f hf g hc := by
  ext c
  apply cover_injective f hf
  intro i
  rw [ht,glueLinear_loc]

abbrev localizedSections (f : Fin m → R) :=
  ∀ i,Loc (f i) C →ₗ[Localization (Submonoid.powers (f i))] Loc (f i) B

def originalInputs (s : localizedSections (B := B) (C := C) f) (i : Fin m) : C →ₗ[R] Loc (f i) B :=
  (s i).restrictScalars R |>.comp (loc (f i))

/-- Compatibility is evaluated on original elements. Equality of the actual
maps on the overlap implies this equation by evaluation; conversely their
localized extensions are determined by these elements and inverted scalars. -/
def Compatible (s : localizedSections (B := B) (C := C) f) : Prop :=
  ∀ i j c,overlapLeft (f i) (f j) (originalInputs f s i c)=
    overlapRight (f i) (f j) (originalInputs f s j c)

/-- The actual extension of the i-th local map to the common localization. -/
def overlapSectionLeft (s : localizedSections (B := B) (C := C) f) (i j : Fin m) :
    Loc (f i*f j) C →ₗ[R] Loc (f i*f j) B :=
  IsLocalizedModule.lift (Submonoid.powers (f i*f j)) (loc (f i*f j))
    ((overlapLeft (f i) (f j)).comp (originalInputs f s i))
    (IsLocalizedModule.map_units (loc (M := B) (f i*f j)))

def overlapSectionRight (s : localizedSections (B := B) (C := C) f) (i j : Fin m) :
    Loc (f i*f j) C →ₗ[R] Loc (f i*f j) B :=
  IsLocalizedModule.lift (Submonoid.powers (f i*f j)) (loc (f i*f j))
    ((overlapRight (f i) (f j)).comp (originalInputs f s j))
    (IsLocalizedModule.map_units (loc (M := B) (f i*f j)))

@[simp] theorem overlapSectionLeft_loc (s : localizedSections (B := B) (C := C) f)
    (i j : Fin m) (c : C) :
    overlapSectionLeft f s i j (loc (f i*f j) c)=
      overlapLeft (f i) (f j) (originalInputs f s i c) := IsLocalizedModule.lift_apply ..

@[simp] theorem overlapSectionRight_loc (s : localizedSections (B := B) (C := C) f)
    (i j : Fin m) (c : C) :
    overlapSectionRight f s i j (loc (f i*f j) c)=
      overlapRight (f i) (f j) (originalInputs f s j c) := IsLocalizedModule.lift_apply ..

theorem compatible_iff_overlap_maps_equal (s : localizedSections (B := B) (C := C) f) :
    Compatible f s ↔ ∀ i j,overlapSectionLeft f s i j=overlapSectionRight f s i j := by
  constructor
  · intro h i j
    apply IsLocalizedModule.ext (Submonoid.powers (f i*f j)) (loc (M := C) (f i*f j))
      (IsLocalizedModule.map_units (loc (M := B) (f i*f j)))
    ext c
    simpa only [LinearMap.comp_apply,overlapSectionLeft_loc,overlapSectionRight_loc] using h i j c
  · intro h i j c
    have hc := LinearMap.congr_fun (h i j) (loc (f i*f j) c)
    simpa only [overlapSectionLeft_loc,overlapSectionRight_loc] using hc

def gluedSection (s : localizedSections (B := B) (C := C) f) (hc : Compatible f s) : C →ₗ[R] B :=
  glueLinear f hf (originalInputs f s) hc

theorem localized_gluedSection (s : localizedSections (B := B) (C := C) f)
    (hc : Compatible f s) (i : Fin m) :
    LocalizedModule.map (Submonoid.powers (f i)) (gluedSection f hf s hc)=s i := by
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.ext (Submonoid.powers (f i)) (loc (M := C) (f i))
    (IsLocalizedModule.map_units (loc (M := B) (f i)))
  apply LinearMap.ext
  intro c
  change LocalizedModule.map (Submonoid.powers (f i)) (gluedSection f hf s hc)
      (LocalizedModule.mk c 1)=s i (loc (f i) c)
  rw [LocalizedModule.map_mk]
  exact glueLinear_loc f hf (originalInputs f s) hc c i

theorem gluedSection_right_inverse (q : B →ₗ[R] C)
    (s : localizedSections (B := B) (C := C) f) (hc : Compatible f s)
    (hs : ∀ i,(LocalizedModule.map (Submonoid.powers (f i)) q).comp (s i)=LinearMap.id) :
    q.comp (gluedSection f hf s hc)=LinearMap.id := by
  apply LinearMap.ext
  intro c
  apply cover_injective f hf
  intro i
  have h := LinearMap.congr_fun (hs i) (loc (f i) c)
  rw [← localized_gluedSection f hf s hc i] at h
  change LocalizedModule.map (Submonoid.powers (f i)) q
    (LocalizedModule.map (Submonoid.powers (f i)) (gluedSection f hf s hc) (LocalizedModule.mk c 1))=
    LocalizedModule.mk c 1 at h
  simpa only [LocalizedModule.map_mk] using h

include hf in
theorem sections_glue_uniquely (q : B →ₗ[R] C)
    (s : localizedSections (B := B) (C := C) f) (hc : Compatible f s)
    (hs : ∀ i,(LocalizedModule.map (Submonoid.powers (f i)) q).comp (s i)=LinearMap.id) :
    ∃! t : C →ₗ[R] B,q.comp t=LinearMap.id ∧
      ∀ i,LocalizedModule.map (Submonoid.powers (f i)) t=s i := by
  refine ⟨gluedSection f hf s hc,
    ⟨gluedSection_right_inverse f hf q s hc hs,localized_gluedSection f hf s hc⟩,?_⟩
  intro t ht
  apply glueLinear_unique f hf (originalInputs f s) hc t
  intro i c
  have h := LinearMap.congr_fun (ht.2 i) (loc (f i) c)
  simpa only [loc,LocalizedModule.mkLinearMap_apply,LocalizedModule.map_mk,originalInputs,
    LinearMap.comp_apply,LinearMap.restrictScalars_apply] using h

end MathGauge.GluedSections
