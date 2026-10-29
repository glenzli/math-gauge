import ProfiniteDescent

noncomputable section
open CategoryTheory Opposite
universe u g w
namespace MathGauge.Descent
variable {Γ : Type g} [Group Γ]
variable {H : ProfSheaf.{u,w}} (A : PAction (Γ := Γ) H.obj)

theorem quotient_eq_iff_finite_cover (U : Profinite.{u}) (x y : H.obj.obj (op U)) :
    (A.quotient_projection ProfSite).app (op U) x =
      (A.quotient_projection ProfSite).app (op U) y ↔
    ∃ (ι : Type) (_ : Finite ι) (V : ι → Profinite.{u}) (f : (i : ι) → V i ⟶ U),
      (∀ t : U, ∃ (i : ι) (s : V i), f i s = t) ∧
      ∀ i, ∃ a : Γ, (A.act a).app (op (V i)) (H.obj.map (f i).op x) =
        H.obj.map (f i).op y := by
  rw [A.quotient_eq_iff_local_orbit,prof_cover_iff]
  rfl

abbrev ProfPoint : Profinite.{u} := Profinite.of PUnit.{u+1}

theorem prof_point_cover_id {S : Sieve ProfPoint.{u}} (hS : S ∈ ProfSite ProfPoint) :
    S (𝟙 ProfPoint) := by
  obtain ⟨ι,hι,V,f,hf,hS⟩ := (prof_cover_iff S).mp hS
  obtain ⟨i,y,hy⟩ := hf PUnit.unit
  let c : ProfPoint ⟶ V i := CompHausLike.ofHom _ (ContinuousMap.const _ y)
  have hc : c ≫ f i = 𝟙 ProfPoint := by ext z
  simpa only [hc] using S.downward_closed (hS i) c

theorem prof_point_locally_surjective {F G : Profinite.{u}ᵒᵖ ⥤ Type (max (u+1) w)}
    (f : F ⟶ G) [Presheaf.IsLocallySurjective ProfSite f] :
    Function.Surjective (f.app (op ProfPoint)) := by
  intro y
  have h := prof_point_cover_id (Presheaf.imageSieve_mem ProfSite f y)
  obtain ⟨x,hx⟩ := h
  refine ⟨x,?_⟩
  simpa using hx

theorem quotient_point_eq_iff (x y : H.obj.obj (op ProfPoint)) :
    (A.quotient_projection ProfSite).app (op ProfPoint) x =
      (A.quotient_projection ProfSite).app (op ProfPoint) y ↔
      ∃ a : Γ, (A.act a).app (op ProfPoint) x = y := by
  rw [A.quotient_eq_iff_local_orbit]
  constructor
  · intro h
    have hi := prof_point_cover_id h
    change ∃ a : Γ, (A.act a).app (op ProfPoint)
      (H.obj.map (𝟙 ProfPoint).op x) = H.obj.map (𝟙 ProfPoint).op y at hi
    simp only [op_id] at hi
    rw [H.obj.map_id] at hi
    exact hi
  · rintro ⟨a,ha⟩
    have hq := congrArg (fun z => (A.quotient_projection ProfSite).app (op ProfPoint) z) ha
    have hinv := congrArg (fun η => η.app (op ProfPoint) x) (A.quotient_invariant ProfSite a)
    exact (A.quotient_eq_iff_local_orbit ProfSite _ x y).mp (hinv.symm.trans hq)

/-- Sheafification leaves the singleton orbit set unchanged, proved from its covers. -/
def quotient_point_equiv :
    Quotient (A.orbit_setoid (op ProfPoint)) ≃
      (A.quotient_sheaf ProfSite).obj.obj (op ProfPoint) :=
  Equiv.ofBijective ((ProfSite.toSheafify A.orbit_presheaf).app (op ProfPoint)) (by
    constructor
    · intro x y h
      induction x using Quotient.inductionOn with
      | h x =>
        induction y using Quotient.inductionOn with
        | h y =>
          apply Quotient.sound
          exact (quotient_point_eq_iff A x y).mp h
    · exact prof_point_locally_surjective _)

end MathGauge.Descent
