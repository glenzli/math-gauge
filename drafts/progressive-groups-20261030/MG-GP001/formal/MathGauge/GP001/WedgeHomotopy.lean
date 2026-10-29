import MathGauge.GP001.ConstantConeWedge

/-! Explicit pointed maps and relative homotopies on the actual binary wedge. -/
namespace MathGauge.GP001
noncomputable section
open ContinuousMap Set Topology unitInterval MathGauge.PublicProof.Topology

universe u v w z
variable {L : Type u} [TopologicalSpace L] [Nonempty L]
variable {D : Type v} [TopologicalSpace D] {E : Type w} [TopologicalSpace E]
variable {Z : Type z} [TopologicalSpace Z]

def wedgeLift (d : D) (f : C(D, Z)) (g : C(Susp L, Z)) (h : g (Susp.south L) = f d) :
    C(BaseSuspensionWedge (L := L) d, Z) := by
  let F : C(D ⊕ Susp L, Z) := ⟨Sum.elim f g, f.continuous.sumElim g.continuous⟩
  have hc : ∀ x ∈ ({Sum.inl d, Sum.inr (Susp.south L)} : Set (D ⊕ Susp L)), F x = f d := by
    intro x hx
    rcases hx with rfl | hx
    · rfl
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact h
  exact ⟨Quotient.lift F (by
    intro a b hab
    rcases hab with rfl | ⟨ha, hb⟩
    · rfl
    · exact (hc a ha).trans (hc b hb).symm), F.continuous.quotient_lift _⟩

@[simp] theorem wedgeLift_base (d : D) (f : C(D, Z)) (g : C(Susp L, Z)) (h) (x : D) :
    wedgeLift d f g h (wedgeBase d x) = f x := rfl

@[simp] theorem wedgeLift_suspension (d : D) (f : C(D, Z)) (g : C(Susp L, Z)) (h)
    (x : Susp L) : wedgeLift d f g h (wedgeSuspension d x) = g x := rfl

/-- A pointed map on the base, with the suspension fixed pointwise. -/
def wedgeMap (d : D) (e : E) (f : C(D, E)) (hf : f d = e) :
    C(BaseSuspensionWedge (L := L) d, BaseSuspensionWedge (L := L) e) :=
  wedgeLift d ((wedgeBase e).comp f) (wedgeSuspension e)
    (by simpa only [comp_apply, hf] using wedge_basepoint (L := L) e)

@[simp] theorem wedgeMap_base (d : D) (e : E) (f : C(D, E)) (hf) (x : D) :
    wedgeMap (L := L) d e f hf (wedgeBase d x) = wedgeBase e (f x) := rfl

@[simp] theorem wedgeMap_suspension (d : D) (e : E) (f : C(D, E)) (hf) (x : Susp L) :
    wedgeMap d e f hf (wedgeSuspension d x) = wedgeSuspension e x := rfl

@[simp] theorem wedgeMap_id (d : D) :
    wedgeMap (L := L) d d (ContinuousMap.id D) rfl = ContinuousMap.id _ := by
  apply DFunLike.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ x => cases x <;> rfl

theorem wedgeMap_comp (d : D) (e : E) (z : Z) (f : C(D, E)) (g : C(E, Z))
    (hf : f d = e) (hg : g e = z) :
    wedgeMap (L := L) d z (g.comp f) (by simp only [comp_apply, hf, hg]) =
      (wedgeMap e z g hg).comp (wedgeMap d e f hf) := by
  apply DFunLike.ext
  intro x
  induction x using Quotient.inductionOn with
  | _ x => cases x <;> rfl

/-- Joint continuity is proved by the product-quotient theorem, not separate continuity. -/
def wedgeMapHomotopy (d : D) (e : E) {f g : C(D, E)}
    (hf : f d = e) (hg : g d = e) (H : f.Homotopy g)
    (hH : ∀ t, H (t, d) = e) :
    (wedgeMap (L := L) d e f hf).Homotopy (wedgeMap d e g hg) := by
  let Ft (t : I) : C(D, E) := ⟨fun x => H (t, x),
    H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let F : I × BaseSuspensionWedge (L := L) d → BaseSuspensionWedge (L := L) e :=
    fun p => wedgeMap d e (Ft p.1) (hH p.1) p.2
  have hF : Continuous F := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    have hd : Continuous (fun p : I × D => wedgeBase (L := L) e (H p)) :=
      (wedgeBase e).continuous.comp H.continuous
    have hs : Continuous (fun p : I × Susp L => wedgeSuspension e p.2) :=
      (wedgeSuspension e).continuous.comp continuous_snd
    convert (hd.sumElim hs).comp (Homeomorph.prodSumDistrib).continuous using 1
    funext p
    rcases p with ⟨t, x | x⟩ <;> rfl
  refine ⟨⟨F, hF⟩, ?_, ?_⟩
  · intro x
    induction x using Quotient.inductionOn with
    | _ x =>
      cases x with
      | inl x => exact congrArg (wedgeBase e) (H.apply_zero x)
      | inr x => rfl
  · intro x
    induction x using Quotient.inductionOn with
    | _ x =>
      cases x with
      | inl x => exact congrArg (wedgeBase e) (H.apply_one x)
      | inr x => rfl

/-- A concrete deformation retract fixing the selected point induces a wedge equivalence. -/
def wedgeSDREquiv (r : C(D, E)) (i : C(E, D)) (hri : ∀ x, r (i x) = x) (e : E)
    (H : (ContinuousMap.id D).Homotopy (i.comp r)) (hH : ∀ t, H (t, i e) = i e) :
    BaseSuspensionWedge (L := L) (i e) ≃ₕ BaseSuspensionWedge (L := L) e where
  toFun := wedgeMap (i e) e r (hri e)
  invFun := wedgeMap e (i e) i rfl
  left_inv := by
    have h : (wedgeMap (L := L) e (i e) i rfl).comp (wedgeMap (i e) e r (hri e)) =
        wedgeMap (i e) (i e) (i.comp r) (by simp only [comp_apply, hri]) :=
      (wedgeMap_comp (i e) e (i e) r i (hri e) rfl).symm
    rw [h]
    have HH := (wedgeMapHomotopy (L := L) (i e) (i e) rfl
      (by simp only [comp_apply, hri]) H hH).symm
    simpa only [wedgeMap_id] using (show Homotopic _ _ from ⟨HH⟩)
  right_inv := by
    have h : (wedgeMap (L := L) (i e) e r (hri e)).comp (wedgeMap e (i e) i rfl) =
        ContinuousMap.id _ := by
      apply DFunLike.ext
      intro x
      induction x using Quotient.inductionOn with
      | _ x =>
        cases x with
        | inl x => exact congrArg (wedgeBase e) (hri x)
        | inr x => rfl
    rw [h]

/-- Change the actual suspended link by a homeomorphism, preserving its south pole. -/
def wedgeLinkHomeomorph {M : Type*} [TopologicalSpace M] [Nonempty M]
    (d : D) (e : L ≃ₜ M) :
    BaseSuspensionWedge (L := L) d ≃ₜ BaseSuspensionWedge (L := M) d where
  toFun := wedgeLift d (wedgeBase d)
    ((wedgeSuspension d).comp (Susp.map (e : C(L, M))))
    (by simp only [comp_apply, Susp.map_south]; exact wedge_basepoint d)
  invFun := wedgeLift d (wedgeBase d)
    ((wedgeSuspension d).comp (Susp.map (e.symm : C(M, L))))
    (by simp only [comp_apply, Susp.map_south]; exact wedge_basepoint d)
  left_inv x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      cases x with
      | inl x => rfl
      | inr x =>
        induction x using Susp.ind with
        | h p =>
          change wedgeSuspension d (Susp.mk (p.1, e.symm (e p.2))) = wedgeSuspension d (Susp.mk p)
          rw [e.symm_apply_apply]
  right_inv x := by
    induction x using Quotient.inductionOn with
    | _ x =>
      cases x with
      | inl x => rfl
      | inr x =>
        induction x using Susp.ind with
        | h p =>
          change wedgeSuspension d (Susp.mk (p.1, e (e.symm p.2))) = wedgeSuspension d (Susp.mk p)
          rw [e.apply_symm_apply]
  continuous_toFun := (wedgeLift _ _ _ _).continuous
  continuous_invFun := (wedgeLift _ _ _ _).continuous

end
end MathGauge.GP001
