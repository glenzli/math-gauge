import MathGauge.GP001.ConstantConeWedge
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

namespace MathGauge.GP001
noncomputable section
open ContinuousMap Set Topology unitInterval

universe u v
variable {L : Type u} {D : Type v} [TopologicalSpace L] [TopologicalSpace D]
  [Nonempty L] [LocallyCompactSpace L]

abbrev attachmentTip (f : C(L, D)) : ConeAttachment f :=
  attachmentCylinder f (1, Classical.arbitrary L)

/-- The cone cylinder as a genuine path in the compact-open mapping space. -/
def attachmentPath (f : C(L, D)) :
    Path ((attachmentBase f).comp f) (const L (attachmentTip f)) where
  toContinuousMap := (attachmentCylinder f).curry
  source' := by ext l; exact attachmentCylinder_zero f l
  target' := by ext l; exact attachmentCylinder_one f l (Classical.arbitrary L)

def attachmentLiftPath {Z : Type*} [TopologicalSpace Z] (f : C(L, D))
    (g : C(D, Z)) (z : Z) (p : Path (g.comp f) (const L z)) : C(ConeAttachment f, Z) :=
  attachmentLift f g p.toContinuousMap.uncurry
    (fun l => congrArg (fun q : C(L, Z) => q l) p.source)
    (fun l l' => (congrArg (fun q : C(L, Z) => q l) p.target).trans
      (congrArg (fun q : C(L, Z) => q l') p.target).symm)

@[simp] theorem attachmentLiftPath_base {Z : Type*} [TopologicalSpace Z]
    (f : C(L, D)) (g : C(D, Z)) (z : Z) (p : Path (g.comp f) (const L z)) (d : D) :
    attachmentLiftPath f g z p (attachmentBase f d) = g d := rfl

@[simp] theorem attachmentLiftPath_cylinder {Z : Type*} [TopologicalSpace Z]
    (f : C(L, D)) (g : C(D, Z)) (z : Z) (p : Path (g.comp f) (const L z)) (t : I) (l : L) :
    attachmentLiftPath f g z p (attachmentCylinder f (t,l)) = p t l := rfl

/-- Paste the specified attaching homotopy before the target cone cylinder. -/
def attachmentMap {f g : C(L, D)} (p : Path f g) : C(ConeAttachment f, ConeAttachment g) :=
  attachmentLiftPath f (attachmentBase g) (attachmentTip g)
    ((p.map (continuous_postcomp (attachmentBase g))).trans (attachmentPath g))

@[simp] theorem attachmentMap_base {f g : C(L, D)} (p : Path f g) (d : D) :
    attachmentMap p (attachmentBase f d) = attachmentBase g d := rfl

theorem attachmentMap_comp_cylinder {f g : C(L, D)} (p : Path f g) (t : I) (l : L) :
    attachmentMap p.symm (attachmentMap p (attachmentCylinder f (t,l))) =
      ((p.map (continuous_postcomp (attachmentBase f))).trans
        ((p.map (continuous_postcomp (attachmentBase f))).symm.trans (attachmentPath f))) t l := by
  change attachmentMap p.symm
    (((p.map (continuous_postcomp (attachmentBase g))).trans (attachmentPath g)) t l) = _
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs with h
  · rfl
  · rfl

/-- Cancellation of the attaching homotopy and its reverse descends to an
actual continuous homotopy on the cone quotient. -/
def attachmentMap_inverseHomotopy {f g : C(L, D)} (p : Path f g) :
    Homotopy ((attachmentMap p.symm).comp (attachmentMap p)) (ContinuousMap.id _) := by
  let P := p.map (continuous_postcomp (attachmentBase f))
  let R : Path.Homotopy (P.trans (P.symm.trans (attachmentPath f))) (attachmentPath f) :=
    ((Path.Homotopy.transAssoc P P.symm (attachmentPath f)).symm.trans
      ((Path.Homotopy.reflTransSymm P).symm.hcomp (Path.Homotopy.refl (attachmentPath f)))).trans
        (Path.Homotopy.reflTrans (attachmentPath f))
  let F : I × ConeAttachment f → ConeAttachment f := fun a =>
    attachmentLiftPath f (attachmentBase f) (attachmentTip f) (R.eval a.1) a.2
  have hF : Continuous F := by
    apply isQuotientMap_quot_mk.continuous_lift_prod_right
    let B : I × D → ConeAttachment f := fun q => attachmentBase f q.2
    let C : I × (I × L) → ConeAttachment f := fun q => R (q.1, q.2.1) q.2.2
    have hB : Continuous B := (attachmentBase f).continuous.comp continuous_snd
    have hC : Continuous C := continuous_eval.comp
      ((R.toHomotopy.continuous.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
        (continuous_snd.comp continuous_snd))
    convert (hB.sumElim hC).comp
      (Homeomorph.prodSumDistrib : I × (D ⊕ (I × L)) ≃ₜ (I × D) ⊕ (I × (I × L))).continuous using 1
    funext a
    rcases a with ⟨t, d | c⟩ <;> rfl
  refine { toFun := F
           continuous_toFun := hF
           map_zero_left := ?_
           map_one_left := ?_ }
  · intro z
    induction z using Quot.ind with
    | _ z =>
      cases z with
      | inl d => rfl
      | inr q =>
        change R (0, q.1) q.2 = attachmentMap p.symm
          (attachmentMap p (attachmentCylinder f q))
        rw [R.apply_zero]
        exact (attachmentMap_comp_cylinder p q.1 q.2).symm
  · intro z
    induction z using Quot.ind with
    | _ z =>
      cases z with
      | inl d => rfl
      | inr q =>
        change R (1, q.1) q.2 = attachmentCylinder f q
        rw [R.apply_one]
        rfl

/-- Homotopic attaching maps have homotopy equivalent actual mapping cones. -/
def attachmentHomotopyEquiv {f g : C(L, D)} (p : Path f g) :
    ConeAttachment f ≃ₕ ConeAttachment g where
  toFun := attachmentMap p
  invFun := attachmentMap p.symm
  left_inv := ⟨attachmentMap_inverseHomotopy p⟩
  right_inv := by
    change Nonempty (((attachmentMap p).comp (attachmentMap p.symm)).Homotopy (ContinuousMap.id _))
    have h := attachmentMap_inverseHomotopy p.symm
    simpa only [Path.symm_symm] using (show Nonempty _ from ⟨h⟩)

/-- The full S2 equivalence at the chosen nullhomotopy value d0. The target is
the actual wedge quotient at d0 and the south suspension pole. -/
def nullAttachmentWedgeEquiv (f : C(L, D)) (d0 : D) (H : Homotopy f (const L d0)) :
    ConeAttachment f ≃ₕ BaseSuspensionWedge (L := L) d0 :=
  (attachmentHomotopyEquiv
    ({toContinuousMap := H.curry, source' := H.curry_zero, target' := H.curry_one} :
      Path f (const L d0))).trans (constantAttachmentWedgeHomeomorph d0).toHomotopyEquiv


/-- Moving the wedge point along a path changes neither homotopy type. -/
def wedgeBasepointEquiv (d0 d1 : D) (p : Path d0 d1) :
    BaseSuspensionWedge (L := L) d0 ≃ₕ BaseSuspensionWedge (L := L) d1 :=
  (constantAttachmentWedgeHomeomorph d0).symm.toHomotopyEquiv.trans
    ((attachmentHomotopyEquiv (p.map (continuous_const' (X := L)))).trans
      (constantAttachmentWedgeHomeomorph d1).toHomotopyEquiv)

theorem wedgeBasepoint_independent [PathConnectedSpace D] (d0 d1 : D) :
    Nonempty (BaseSuspensionWedge (L := L) d0 ≃ₕ BaseSuspensionWedge (L := L) d1) :=
  ⟨wedgeBasepointEquiv d0 d1 (PathConnectedSpace.joined d0 d1).somePath⟩

omit [Nonempty L] [LocallyCompactSpace L] in
/-- Finite CW compactness is proved from the actual finite family of closed
cells, so the source of the attaching map needs no added compactness assumption. -/
theorem finite_cw_isCompact (C : Set D) [CWComplex C] [CWComplex.Finite C] :
    IsCompact C := by
  letI : Finite (Σ n, RelCWComplex.cell C n) := RelCWComplex.finite_cells_of_finite (C := C)
  have h : IsCompact (⋃ p : Σ n, RelCWComplex.cell C n,
      RelCWComplex.closedCell (C := C) p.1 p.2) :=
    isCompact_iUnion fun _ => RelCWComplex.isCompact_closedCell
  simpa only [iUnion_sigma, CWComplex.union] using h

omit [Nonempty L] [LocallyCompactSpace L] in
/-- The task's actual finite CW subcomplex inclusion. The nonempty subtype L
is compact by the preceding theorem. D is not assumed contractible. -/
theorem finite_cw_null_attachment_wedge [T2Space D]
    [CWComplex (Set.univ : Set D)] [CWComplex.Finite (Set.univ : Set D)]
    (A : RelCWComplex.Subcomplex (Set.univ : Set D)) [Nonempty (A : Set D)]
    (hnull : (ContinuousMap.subtypeVal (A : Set D)).Nullhomotopic) :
    ∃ d0 : D, Nonempty (ConeAttachment (ContinuousMap.subtypeVal (A : Set D)) ≃ₕ
      BaseSuspensionWedge (L := (A : Set D)) d0) := by
  letI : CompactSpace (A : Set D) := isCompact_iff_compactSpace.mp (finite_cw_isCompact (A : Set D))
  obtain ⟨d0, ⟨H⟩⟩ := hnull
  exact ⟨d0, ⟨nullAttachmentWedgeEquiv _ d0 H⟩⟩

end
end MathGauge.GP001
