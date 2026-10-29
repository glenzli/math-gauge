import MathGauge.GP001.CollapseContractible
import VendoredSuspension

/-! The actual quotient identification in S2. The attaching map is constant in
this module; ConeHomotopy.lean proves invariance under homotopy of the attaching
map and applies this quotient homeomorphism to the task's nullhomotopy. -/
namespace MathGauge.GP001
noncomputable section
open ContinuousMap Set Topology unitInterval
open MathGauge.PublicProof.Topology

universe u v w
variable {L : Type u} {D : Type v} [TopologicalSpace L] [TopologicalSpace D]

inductive ConeAttachmentRel (f : C(L, D)) : (D ⊕ (I × L)) → (D ⊕ (I × L)) → Prop
  | base (l : L) : ConeAttachmentRel f (.inr (0, l)) (.inl (f l))
  | tip (l l' : L) : ConeAttachmentRel f (.inr (1, l)) (.inr (1, l'))

/-- The actual unreduced mapping cone, with its quotient topology. -/
abbrev ConeAttachment (f : C(L, D)) := Quot (ConeAttachmentRel f)

def attachmentBase (f : C(L, D)) : C(D, ConeAttachment f) :=
  ⟨fun d => Quot.mk _ (.inl d), continuous_quot_mk.comp continuous_inl⟩

def attachmentCylinder (f : C(L, D)) : C(I × L, ConeAttachment f) :=
  ⟨fun p => Quot.mk _ (.inr p), continuous_quot_mk.comp continuous_inr⟩

theorem attachmentCylinder_zero (f : C(L, D)) (l : L) :
    attachmentCylinder f (0, l) = attachmentBase f (f l) :=
  Quot.sound (.base l)

theorem attachmentCylinder_one (f : C(L, D)) (l l' : L) :
    attachmentCylinder f (1, l) = attachmentCylinder f (1, l') :=
  Quot.sound (.tip l l')

def attachmentLift {Z : Type w} [TopologicalSpace Z] (f : C(L, D))
    (g : C(D, Z)) (h : C(I × L, Z))
    (hbase : ∀ l, h (0, l) = g (f l))
    (htip : ∀ l l', h (1, l) = h (1, l')) : C(ConeAttachment f, Z) :=
  ⟨Quot.lift (Sum.elim g h) (by
      intro a b hr
      cases hr with
      | base l => exact hbase l
      | tip l l' => exact htip l l'),
    continuous_quot_lift _ (g.continuous.sumElim h.continuous)⟩

@[simp] theorem attachmentLift_base {Z : Type w} [TopologicalSpace Z] (f : C(L, D))
    (g : C(D, Z)) (h : C(I × L, Z)) (hbase) (htip) (d : D) :
    attachmentLift f g h hbase htip (attachmentBase f d) = g d := rfl

@[simp] theorem attachmentLift_cylinder {Z : Type w} [TopologicalSpace Z] (f : C(L, D))
    (g : C(D, Z)) (h : C(I × L, Z)) (hbase) (htip) (p : I × L) :
    attachmentLift f g h hbase htip (attachmentCylinder f p) = h p := rfl

variable [Nonempty L]

/-- The actual binary wedge at d0 and the south pole, as a quotient of the
disjoint union. Only these two specified points are identified. -/
abbrev BaseSuspensionWedge (d0 : D) :=
  Collapsed ({Sum.inl d0, Sum.inr (Susp.south L)} : Set (D ⊕ Susp L))

def wedgeBase (d0 : D) : C(D, BaseSuspensionWedge (L := L) d0) :=
  (collapseMap _).comp ⟨Sum.inl, continuous_inl⟩

def wedgeSuspension (d0 : D) : C(Susp L, BaseSuspensionWedge (L := L) d0) :=
  (collapseMap _).comp ⟨Sum.inr, continuous_inr⟩

theorem wedge_basepoint (d0 : D) :
    wedgeSuspension (L := L) d0 (Susp.south L) = wedgeBase d0 d0 := by
  apply Quotient.sound
  right
  exact ⟨by simp, by simp⟩

def constantAttachmentToWedge (d0 : D) :
    C(ConeAttachment (const L d0), BaseSuspensionWedge (L := L) d0) :=
  attachmentLift (const L d0) (wedgeBase d0) ((wedgeSuspension d0).comp Susp.mk)
    (fun l => by simp only [comp_apply, Susp.mk_zero]; exact wedge_basepoint d0)
    (fun l l' => congrArg (wedgeSuspension d0) (Susp.mk_one_eq_mk_one l l'))

def suspensionToConstantAttachment (d0 : D) : C(Susp L, ConeAttachment (const L d0)) :=
  Susp.lift (attachmentCylinder (const L d0))
    (fun l l' => (attachmentCylinder_zero (const L d0) l).trans
      (attachmentCylinder_zero (const L d0) l').symm)
    (attachmentCylinder_one (const L d0))

theorem suspensionToConstantAttachment_south (d0 : D) :
    suspensionToConstantAttachment (L := L) d0 (Susp.south L) =
      attachmentBase (const L d0) d0 :=
  attachmentCylinder_zero (const L d0) (Classical.arbitrary L)

def wedgeToConstantAttachment (d0 : D) :
    C(BaseSuspensionWedge (L := L) d0, ConeAttachment (const L d0)) := by
  let h : C(D ⊕ Susp L, ConeAttachment (const L d0)) :=
    ⟨Sum.elim (attachmentBase (const L d0)) (suspensionToConstantAttachment d0),
      (attachmentBase (const L d0)).continuous.sumElim
        (suspensionToConstantAttachment d0).continuous⟩
  have hc : ∀ z ∈ ({Sum.inl d0, Sum.inr (Susp.south L)} : Set (D ⊕ Susp L)),
      h z = attachmentBase (const L d0) d0 := by
    intro z hz
    rcases hz with rfl | hz
    · rfl
    · obtain rfl := Set.mem_singleton_iff.mp hz
      exact suspensionToConstantAttachment_south d0
  exact ⟨Quotient.lift h (by
    intro a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · rfl
    · exact (hc a ha).trans (hc b hb).symm), h.continuous.quotient_lift _⟩

/-- Constant cone attachment really is D wedged with the unreduced suspension;
the selected wedge points are explicit. -/
def constantAttachmentWedgeHomeomorph (d0 : D) :
    ConeAttachment (const L d0) ≃ₜ BaseSuspensionWedge (L := L) d0 where
  toFun := constantAttachmentToWedge d0
  invFun := wedgeToConstantAttachment d0
  left_inv z := by
    induction z using Quot.ind with
    | _ z =>
      cases z with
      | inl d => rfl
      | inr p => rfl
  right_inv z := by
    induction z using Quotient.ind with
    | _ z =>
      cases z with
      | inl d => rfl
      | inr p =>
        induction p using Susp.ind with
        | _ p => rfl
  continuous_toFun := (constantAttachmentToWedge d0).continuous
  continuous_invFun := (wedgeToConstantAttachment d0).continuous

end
end MathGauge.GP001
