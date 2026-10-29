import PointInvisibleAction
import LocalBaseDetection

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite
namespace MathGauge.Descent.Noncovering

abbrev X := PUnit ⊕ Bool
abbrev H : ProfSheaf.{0,0} := prof_probe_sheaf Bool
abbrev ESheaf : ProfSheaf.{0,0} := prof_probe_sheaf X
abbrev B : ProfSheaf.{0,0} := prof_probe_sheaf PUnit

def baseSpaceAction : SpaceAction TwoGroup Bool where
  act _ := Homeomorph.refl _
  one _ := rfl
  mul _ _ _ := rfl

abbrev baseAction : PAction.{1,0,0,0} (Γ := TwoGroup) H.obj :=
  SpaceAction.probe_action.{0,0,0} baseSpaceAction

def flip : X → X
  | .inl t => .inl t
  | .inr b => .inr (!b)

theorem flip_involution (x : X) : flip (flip x)=x := by
  cases x with
  | inl t => rfl
  | inr b => cases b <;> rfl

def flipHom : ESheaf ⟶ ESheaf :=
  ⟨(MathGauge.Mapping.lift_nat_equiv _ _) (MathGauge.Mapping.probe_post
    ⟨flip,continuous_of_discreteTopology⟩)⟩

theorem flipHom_involution : flipHom ≫ flipHom=𝟙 ESheaf := by
  apply Sheaf.hom_ext
  ext U f x
  exact flip_involution (f.down x)

def projectionValue : X → Bool
  | .inl _ => false
  | .inr _ => true

def projection : ESheaf ⟶ H :=
  ⟨(MathGauge.Mapping.lift_nat_equiv _ _) (MathGauge.Mapping.probe_post
    ⟨projectionValue,continuous_of_discreteTopology⟩)⟩

def record : EquivariantOver baseAction where
  sheaf := ESheaf
  projection := projection
  action := involution_action ESheaf flipHom flipHom_involution
  equivariant a := by
    ext U f x
    change projectionValue
      (((if a.toAdd.val=0 then (𝟙 ESheaf.obj) else flipHom.hom).app U f).down x) =
      projectionValue (f.down x)
    split
    · rfl
    · change projectionValue (flip (f.down x))=projectionValue (f.down x)
      cases f.down x <;> rfl

def inclusion : B ⟶ H :=
  ⟨(MathGauge.Mapping.lift_nat_equiv _ _) (MathGauge.Mapping.probe_post
    (ContinuousMap.const _ false))⟩

def baseMap : B ⟶ baseAction.quotient_sheaf ProfSite := inclusion ≫ quotient_hom baseAction

theorem nonempty_representable_base : Nonempty (B.obj.obj (op ProfPoint)) :=
  ⟨⟨ContinuousMap.const _ PUnit.unit⟩⟩

theorem base_quotient_injective (U : Profiniteᵒᵖ) :
    Function.Injective ((baseAction.quotient_projection ProfSite).app U) := by
  intro f h he
  have hcov := (baseAction.quotient_eq_iff_local_orbit ProfSite U f h).mp he
  apply (((isSheaf_iff_isSheaf_of_type ProfSite _).mp H.property).isSeparated _ hcov).ext
  intro V v hv
  obtain ⟨a,ha⟩ := hv
  exact ha

theorem original_not_realizable : ¬ record.Realizable := by
  rw [record.realizable_iff_stabilizer_trivial]
  intro hs
  let x : ESheaf.obj.obj (op ProfPoint) := ⟨ContinuousMap.const _ (.inr false)⟩
  have h := hs (op ProfPoint) x (Multiplicative.ofAdd (1 : ZMod 2)) rfl
  have he := congrArg (fun f => f.down PUnit.unit) h
  change Sum.inr true=Sum.inr false at he
  cases he

theorem pulled_stabilizers_trivial :
    (basechange_record baseAction B baseMap record).StabilizerTrivial := by
  intro U z a _
  have hp : projection.hom.app U z.val.1=inclusion.hom.app U z.val.2 :=
    base_quotient_injective U z.property
  have hz (x : U.unop) : z.val.1.down x=Sum.inl PUnit.unit := by
    have h := congrArg (fun f => f.down x) hp
    change projectionValue (z.val.1.down x)=false at h
    cases he : z.val.1.down x with
    | inl t => exact congrArg Sum.inl (Subsingleton.elim _ _)
    | inr b => rw [he] at h; cases h
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  change ((if a.toAdd.val=0 then (𝟙 ESheaf.obj) else flipHom.hom).app U z.val.1)=z.val.1
  split
  · rfl
  · apply ULift.ext
    ext x
    change flip (z.val.1.down x)=z.val.1.down x
    rw [hz]
    rfl

theorem pulled_realizable : (basechange_record baseAction B baseMap record).Realizable :=
  (basechange_record baseAction B baseMap record).realizable_iff_stabilizer_trivial.mpr
    pulled_stabilizers_trivial

theorem baseMap_not_locally_surjective : ¬ Presheaf.IsLocallySurjective ProfSite baseMap.hom := by
  intro h
  letI := h
  exact original_not_realizable
    ((realizable_iff_local_base.{1,0,0,0} baseAction B baseMap record).mpr pulled_realizable)

end MathGauge.Descent.Noncovering
