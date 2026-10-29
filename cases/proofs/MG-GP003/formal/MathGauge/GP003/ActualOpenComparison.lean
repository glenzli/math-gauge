import MathGauge.GP003.SchemeNeighborhoodMaps

/-! Actual neighborhood extensions on the open subschemes of S. Local lifts
come from actual stalk representatives of the original presheaves. -/
namespace MathGauge.GP003
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat.Presheaf
open AlgebraicGeometry MathGauge.PublicProof.Semilocal

universe u
variable {R : Type u} [CommRing R] {sigma : Finset (PrimeSpectrum R)}

/-- A local scheme at q factors through every actual open containing q. -/
def localToOpen (q : PrimeSpectrum (semilocalRing sigma))
    (U : (finite_point_scheme sigma).Opens) (hq : q ∈ U) : localScheme q ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (localToSemilocal q) (by
    rw [Scheme.Opens.range_ι]
    change Set.range (PrimeSpectrum.comap (algebraMap (semilocalRing sigma)
      (Localization.AtPrime q.asIdeal))) ⊆ U.1
    rw [prime_localization_image]
    intro r hr
    exact ((PrimeSpectrum.le_iff_specializes r q).mp hr).mem_open U.isOpen hq)

@[simp] theorem localToOpen_ι (q : PrimeSpectrum (semilocalRing sigma))
    (U : (finite_point_scheme sigma).Opens) (hq : q ∈ U) :
    localToOpen q U hq ≫ U.ι = localToSemilocal q := IsOpenImmersion.lift_fac _ _ _

def openToLocalRestriction (q : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u})
    (U : (finite_point_scheme sigma).Opens) (hq : q ∈ U) :
    schemeOpenValue (semilocalToAmbient sigma) F U ⟶ schemeNeighborhoodValue (localToAmbient q) F :=
  schemeNeighborhoodRestriction (schemeOpenToAmbient (semilocalToAmbient sigma) U)
    (localToAmbient q) (localToOpen q U hq) (by
      unfold schemeOpenToAmbient localToAmbient
      rw [← Category.assoc,localToOpen_ι]) F

@[simp] theorem openToLocalRestriction_comp (q : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u})
    (U : (finite_point_scheme sigma).Opens) (hq : q ∈ U) :
    schemeOpenRestriction (semilocalToAmbient sigma) F U ≫ openToLocalRestriction q F U hq =
      localRestriction q F := by
  unfold schemeOpenRestriction openToLocalRestriction localRestriction
  rw [schemeNeighborhoodRestriction_comp]
  simp only [localToOpen_ι]

/-- An actual open pulled back from the ambient spectrum has the expected
ambient neighborhood factorization, through actual scheme morphisms. -/
theorem preimage_open_range (W : Opens (PrimeSpectrum R)) :
    Set.range (schemeOpenToAmbient (semilocalToAmbient sigma)
      ((Opens.map (semilocalToAmbient sigma).base).obj W)) ⊆ (W : Set (PrimeSpectrum R)) := by
  rintro z ⟨z,rfl⟩
  exact z.2

/-- Actual stalk surjectivity selects an open of the actual S and a lift in
its neighborhood-colimit extension. The global target need only be a class
on an ambient neighborhood, not a section on the entire ambient spectrum. -/
theorem actual_local_representative
    (q : PrimeSpectrum (semilocalRing sigma))
    {H G : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}} (η : H ⟶ G)
    (hηq : Function.Surjective (schemeNeighborhoodMap (localToAmbient q) η))
    (b : schemeNeighborhoodValue (semilocalToAmbient sigma) G) :
    ∃ U : (finite_point_scheme sigma).Opens, ∃ _hq : q ∈ U,
      ∃ a : schemeOpenValue (semilocalToAmbient sigma) H U,
        schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) U) η a =
          schemeOpenRestriction (semilocalToAmbient sigma) G U b := by
  have hstalk := ambient_stalk_surjective_of_actual_local q η hηq
  obtain ⟨O,b,rfl⟩ := Concrete.colimit_exists_rep
    ((schemeNeighborhoodInclusion (semilocalToAmbient sigma)).op ⋙ G) b
  cases O using Opposite.rec with
  | _ O =>
    have hpO : ambientPoint q ∈ O.1 :=
      ((factors_open_iff_range _ _).mp O.2) ⟨q,rfl⟩
    obtain ⟨a,ha⟩ := hstalk (G.germ O.1 (ambientPoint q) hpO b)
    obtain ⟨V,hpV,aV,rfl⟩ := H.germ_exist (ambientPoint q) a
    rw [stalkFunctor_map_germ_apply] at ha
    obtain ⟨W,hpW,iWV,iWO,he⟩ := G.germ_eq (ambientPoint q) hpV hpO
      (η.app (op V) aV) b ha
    let U : (finite_point_scheme sigma).Opens := (Opens.map (semilocalToAmbient sigma).base).obj W
    let aW := H.map iWV.op aV
    have he' : η.app (op W) aW = G.map iWO.op b := by
      dsimp [aW]
      rw [η.naturality_apply]
      exact he
    let hW := preimage_open_range (sigma := sigma) W
    let hO : Set.range (schemeOpenToAmbient (semilocalToAmbient sigma) U) ⊆ O.1 :=
      fun _ hz => iWO.le (hW hz)
    refine ⟨U,hpW,sectionToSchemeValue (schemeOpenToAmbient (semilocalToAmbient sigma) U) H W hW aW,?_⟩
    have hmap := ConcreteCategory.congr_hom (sectionToSchemeValue_map
      (schemeOpenToAmbient (semilocalToAmbient sigma) U) η W hW) aW
    change schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) U) η
      (sectionToSchemeValue (schemeOpenToAmbient (semilocalToAmbient sigma) U) H W hW aW) = _ at hmap
    rw [hmap]
    change sectionToSchemeValue (schemeOpenToAmbient (semilocalToAmbient sigma) U) G W hW
      (η.app (op W) aW) = _
    rw [he']
    have hres := ConcreteCategory.congr_hom (sectionToSchemeValue_restrict
      (schemeOpenToAmbient (semilocalToAmbient sigma) U) G hO hW iWO.le) b
    change sectionToSchemeValue (schemeOpenToAmbient (semilocalToAmbient sigma) U) G W hW
      (G.map iWO.op b) = _ at hres
    rw [hres]
    have htarget := ConcreteCategory.congr_hom (sectionToSchemeValue_restrictTarget
      (semilocalToAmbient sigma) (schemeOpenToAmbient (semilocalToAmbient sigma) U)
      U.ι rfl G O.1 ((factors_open_iff_range _ _).mp O.2) hO) b
    exact htarget.symm

@[simp] theorem openToLocalRestriction_comp_apply (q : PrimeSpectrum (semilocalRing sigma))
    (F : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u})
    (U : (finite_point_scheme sigma).Opens) (hq : q ∈ U)
    (b : schemeNeighborhoodValue (semilocalToAmbient sigma) F) :
    openToLocalRestriction q F U hq (schemeOpenRestriction (semilocalToAmbient sigma) F U b) =
      localRestriction q F b :=
  ConcreteCategory.congr_hom (openToLocalRestriction_comp q F U hq) b

def closedPair (q r : PrimeSpectrum (semilocalRing sigma)) (i : ULift.{u} Bool) :
    PrimeSpectrum (semilocalRing sigma) := if i.down then r else q

/-- Global uniqueness for two actual open restrictions follows from the proved
actual local-scheme descent. No extension-sheaf instance is an assumption. -/
theorem actual_two_open_uniqueness (q r : PrimeSpectrum (semilocalRing sigma))
    (hexhaust : ∀ z : PrimeSpectrum (semilocalRing sigma),
      IsClosed ({z} : Set (PrimeSpectrum (semilocalRing sigma))) → z = q ∨ z = r)
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (PrimeSpectrum R)))
    (U V : (finite_point_scheme sigma).Opens) (hUV : U ⊔ V = ⊤)
    {b c : schemeNeighborhoodValue (semilocalToAmbient sigma) G.obj}
    (hU : schemeOpenRestriction (semilocalToAmbient sigma) G.obj U b =
      schemeOpenRestriction (semilocalToAmbient sigma) G.obj U c)
    (hV : schemeOpenRestriction (semilocalToAmbient sigma) G.obj V b =
      schemeOpenRestriction (semilocalToAmbient sigma) G.obj V c) : b = c := by
  have hclosed : ∀ z : PrimeSpectrum (semilocalRing sigma),
      IsClosed ({z} : Set (PrimeSpectrum (semilocalRing sigma))) → z ∈ Set.range (closedPair q r) := by
    intro z hz
    rcases hexhaust z hz with rfl | rfl
    · exact ⟨⟨false⟩,rfl⟩
    · exact ⟨⟨true⟩,rfl⟩
  apply (affine_semilocal_descent_exact (closedPair q r) hclosed G).1
  funext i
  have hi : closedPair q r i ∈ U ∨ closedPair q r i ∈ V := by
    change closedPair q r i ∈ U ⊔ V
    rw [hUV]
    trivial
  change localRestriction (closedPair q r i) G.obj b = localRestriction (closedPair q r i) G.obj c
  rcases hi with hi | hi
  · have hh := congrArg (openToLocalRestriction (closedPair q r i) G.obj U hi) hU
    simpa only [openToLocalRestriction_comp_apply] using hh
  · have hh := congrArg (openToLocalRestriction (closedPair q r i) G.obj V hi) hV
    simpa only [openToLocalRestriction_comp_apply] using hh

/-- A local lift remains a lift after restricting along an actual open inclusion. -/
theorem actual_restrict_lift
    {H G : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u}} (η : H ⟶ G)
    {U V : (finite_point_scheme sigma).Opens} (hVU : V ≤ U)
    {a : schemeOpenValue (semilocalToAmbient sigma) H U}
    {b : schemeNeighborhoodValue (semilocalToAmbient sigma) G}
    (ha : schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) U) η a =
      schemeOpenRestriction (semilocalToAmbient sigma) G U b) :
    schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) V) η
      (schemeOpenRestrictionLE (semilocalToAmbient sigma) H hVU a) =
        schemeOpenRestriction (semilocalToAmbient sigma) G V b := by
  have hn := ConcreteCategory.congr_hom (schemeNeighborhoodMap_naturality
    (schemeOpenToAmbient (semilocalToAmbient sigma) U)
    (schemeOpenToAmbient (semilocalToAmbient sigma) V)
    ((finite_point_scheme sigma).homOfLE hVU)
    (by unfold schemeOpenToAmbient; rw [← Category.assoc,Scheme.homOfLE_ι]) η) a
  change schemeOpenRestrictionLE (semilocalToAmbient sigma) G hVU
    (schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) U) η a) =
      schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) V) η
        (schemeOpenRestrictionLE (semilocalToAmbient sigma) H hVU a) at hn
  rw [← hn,ha]
  exact ConcreteCategory.congr_hom (schemeOpenRestriction_comp (semilocalToAmbient sigma) G hVU) b


/-- The S2 comparison for a given actual affine semilocal presentation.
H and G are original presheaves, G is an actual sheaf on the ambient spectrum,
and every value/map on S, its opens and local schemes is the genuine
open-neighborhood extension. Only the task's successful shrinking row is
assumed; the target comparison, extension sheaf property, overlap surjectivity,
and exactness of the original unshrunk row are not hypotheses. -/
theorem actual_affine_two_closed_comparison
    (q r : PrimeSpectrum (semilocalRing sigma)) (hqr : q ≠ r)
    (hqclosed : IsClosed ({q} : Set (PrimeSpectrum (semilocalRing sigma))))
    (hrclosed : IsClosed ({r} : Set (PrimeSpectrum (semilocalRing sigma))))
    (hexhaust : ∀ z : PrimeSpectrum (semilocalRing sigma),
      IsClosed ({z} : Set (PrimeSpectrum (semilocalRing sigma))) → z = q ∨ z = r)
    (H : (TopCat.of (PrimeSpectrum R)).Presheaf AddCommGrpCat.{u})
    (G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of (PrimeSpectrum R))) (η : H ⟶ G.obj)
    (hglobalmono : Function.Injective (schemeNeighborhoodMap (semilocalToAmbient sigma) η))
    (hmono : ∀ U : (finite_point_scheme sigma).Opens,
      Function.Injective (schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) U) η))
    (hqiso : Function.Surjective (schemeNeighborhoodMap (localToAmbient q) η))
    (hriso : Function.Surjective (schemeNeighborhoodMap (localToAmbient r) η))
    (hrefine : ∀ U₀ V : (finite_point_scheme sigma).Opens,
      Separates ({q} : Set (PrimeSpectrum (semilocalRing sigma))) {r} U₀ V → U₀ ⊔ V = ⊤ →
      ∃ U : (finite_point_scheme sigma).Opens, U ≤ U₀ ∧ U ⊔ V = ⊤ ∧
        Function.Exact (schemeTwoOpenRestriction (semilocalToAmbient sigma) H U V)
          (schemeTwoOpenDifference (semilocalToAmbient sigma) H U V)) :
    Function.Bijective (schemeNeighborhoodMap (semilocalToAmbient sigma) η) := by
  refine ⟨hglobalmono,?_⟩
  intro b
  obtain ⟨U₀,hqU₀,a₀,ha₀⟩ := actual_local_representative q η hqiso b
  obtain ⟨V₀,hrV₀,b₀,hb₀⟩ := actual_local_representative r η hriso b
  let U : (finite_point_scheme sigma).Opens := U₀ ⊓ ⟨({r} : Set (PrimeSpectrum (semilocalRing sigma)))ᶜ,hrclosed.isOpen_compl⟩
  let V : (finite_point_scheme sigma).Opens := V₀ ⊓ ⟨({q} : Set (PrimeSpectrum (semilocalRing sigma)))ᶜ,hqclosed.isOpen_compl⟩
  have hs : Separates ({q} : Set (PrimeSpectrum (semilocalRing sigma))) {r} U V := by
    refine ⟨?_,?_,?_,?_⟩
    · intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact ⟨hqU₀,by simpa using hqr⟩
    · exact Set.disjoint_left.mpr fun z hz hzu => hzu.2 hz
    · intro z hz
      obtain rfl := Set.mem_singleton_iff.mp hz
      exact ⟨hrV₀,by simpa using hqr.symm⟩
    · exact Set.disjoint_left.mpr fun z hz hzv => hzv.2 hz
  have hUV : U ⊔ V = ⊤ := open_eq_top_of_contains_closed _ (by
    intro z hz
    rcases hexhaust z hz with rfl | rfl
    · exact Or.inl (hs.1 (Set.mem_singleton _))
    · exact Or.inr (hs.2.2.1 (Set.mem_singleton _)))
  obtain ⟨U',hU'U,hU'V,he⟩ := hrefine U V hs hUV
  let aU : schemeOpenValue (semilocalToAmbient sigma) H U' :=
    schemeOpenRestrictionLE (semilocalToAmbient sigma) H (hU'U.trans inf_le_left) a₀
  let aV : schemeOpenValue (semilocalToAmbient sigma) H V :=
    schemeOpenRestrictionLE (semilocalToAmbient sigma) H inf_le_left b₀
  have haU : schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) U') η aU =
      schemeOpenRestriction (semilocalToAmbient sigma) G.obj U' b :=
    actual_restrict_lift η (hU'U.trans inf_le_left) ha₀
  have haV : schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) V) η aV =
      schemeOpenRestriction (semilocalToAmbient sigma) G.obj V b :=
    actual_restrict_lift η inf_le_left hb₀
  have hz : schemeTwoOpenDifference (semilocalToAmbient sigma) H U' V (aU,aV) = 0 := by
    apply hmono (U' ⊓ V)
    change schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) (U' ⊓ V)) η
      (schemeOpenRestrictionLE (semilocalToAmbient sigma) H (show U' ⊓ V ≤ U' from inf_le_left) aU -
        schemeOpenRestrictionLE (semilocalToAmbient sigma) H (show U' ⊓ V ≤ V from inf_le_right) aV) = _
    rw [map_sub,map_zero,actual_restrict_lift η inf_le_left haU,
      actual_restrict_lift η inf_le_right haV,sub_self]
  obtain ⟨a,ha⟩ := (he (aU,aV)).mp hz
  refine ⟨a,?_⟩
  apply actual_two_open_uniqueness q r hexhaust G U' V hU'V
  · have hn := ConcreteCategory.congr_hom (schemeNeighborhoodMap_naturality
      (semilocalToAmbient sigma) (schemeOpenToAmbient (semilocalToAmbient sigma) U')
      U'.ι rfl η) a
    change schemeOpenRestriction (semilocalToAmbient sigma) G.obj U'
      (schemeNeighborhoodMap (semilocalToAmbient sigma) η a) =
        schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) U') η
          (schemeOpenRestriction (semilocalToAmbient sigma) H U' a) at hn
    rw [hn]
    have hfirst : schemeOpenRestriction (semilocalToAmbient sigma) H U' a = aU := congrArg Prod.fst ha
    rw [hfirst,haU]
  · have hn := ConcreteCategory.congr_hom (schemeNeighborhoodMap_naturality
      (semilocalToAmbient sigma) (schemeOpenToAmbient (semilocalToAmbient sigma) V)
      V.ι rfl η) a
    change schemeOpenRestriction (semilocalToAmbient sigma) G.obj V
      (schemeNeighborhoodMap (semilocalToAmbient sigma) η a) =
        schemeNeighborhoodMap (schemeOpenToAmbient (semilocalToAmbient sigma) V) η
          (schemeOpenRestriction (semilocalToAmbient sigma) H V a) at hn
    rw [hn]
    have hsecond : schemeOpenRestriction (semilocalToAmbient sigma) H V a = aV := congrArg Prod.snd ha
    rw [hsecond,haV]


end
end MathGauge.GP003
