import DeletionConeGluing
import MathGauge.GP001.ConeHomotopy

/-! The exact cone-attachment quotient for a vertex in a finite realization. -/
namespace MathGauge.GP001
noncomputable section
open ContinuousMap MathGauge.PublicProof.Topology
open unitInterval

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (K : PreAbstractSimplicialComplex V) (v : V)
variable [Nonempty (Realization (vertex_link K v))]

/-- The actual barycentric cone map, descended through the defining relations. -/
def coneToRealization :
    C(ConeAttachment (link_to_deletion K v), Realization K) :=
  attachmentLift _ (deletion_to_realization K v) (link_cone_map K v)
    (link_cone_zero K v) (link_cone_one K v)

/-- Its inverse uses the proved quotient presentation by the deletion and link cylinder. -/
def realizationToCone :
    C(Realization K, ConeAttachment (link_to_deletion K v)) :=
  deletion_cone_descend K v (attachmentBase _) (attachmentCylinder _)
    (attachmentCylinder_zero _) (attachmentCylinder_one _)

@[simp] theorem coneToRealization_base (d : Realization (deletion K v)) :
    coneToRealization K v (attachmentBase _ d) = deletion_to_realization K v d := rfl

@[simp] theorem coneToRealization_cylinder (p : I × Realization (vertex_link K v)) :
    coneToRealization K v (attachmentCylinder _ p) = link_cone_point K v p.1 p.2 := rfl

@[simp] theorem realizationToCone_base (d : Realization (deletion K v)) :
    realizationToCone K v (deletion_to_realization K v d) = attachmentBase _ d :=
  deletion_cone_descend_left _ _ _ _ _ _ _

@[simp] theorem realizationToCone_cylinder (t : I) (x : Realization (vertex_link K v)) :
    realizationToCone K v (link_cone_point K v t x) = attachmentCylinder _ (t, x) :=
  deletion_cone_descend_right _ _ _ _ _ _ _ _

/-- No CW replacement occurs: this is the actual finite simplicial realization. -/
def realizationConeHomeomorph :
    Realization K ≃ₜ ConeAttachment (link_to_deletion K v) where
  toFun := realizationToCone K v
  invFun := coneToRealization K v
  left_inv x := by
    obtain ⟨d | ⟨t, x⟩, rfl⟩ := deletion_cone_surjective K v x
    · exact congrArg (coneToRealization K v) (realizationToCone_base K v d)
    · exact congrArg (coneToRealization K v) (realizationToCone_cylinder K v t x)
  right_inv x := by
    induction x using Quot.inductionOn with
    | _ x =>
      cases x with
      | inl d => exact realizationToCone_base K v d
      | inr p => exact realizationToCone_cylinder K v p.1 p.2
  continuous_toFun := (realizationToCone K v).continuous
  continuous_invFun := (coneToRealization K v).continuous

/-- A nullhomotopic actual link inclusion splits off the actual suspended link. -/
def realizationNullLinkWedge (d : Realization (deletion K v))
    (H : (link_to_deletion K v).Homotopy (ContinuousMap.const _ d)) :
    Realization K ≃ₕ BaseSuspensionWedge (L := Realization (vertex_link K v)) d :=
  (realizationConeHomeomorph K v).toHomotopyEquiv.trans
    (nullAttachmentWedgeEquiv _ d H)

end
end MathGauge.GP001
