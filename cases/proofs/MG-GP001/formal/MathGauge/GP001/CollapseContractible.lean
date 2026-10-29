import TauCeti.Topology.Homotopy.Extension.CWComplex
import MathGauge.GP001.Borrowed.CWSubcomplex
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.CompactOpen

/-! S1. Collapse a contractible CW subcomplex. The inverse and both homotopies
are constructed, including continuity of the descended cylinder homotopy. -/

namespace MathGauge.GP001
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology ContinuousMap unitInterval

universe u
variable {Y : Type u} [TopologicalSpace Y]

def collapseSetoid (A : Set Y) : Setoid Y where
  r x y := x = y ∨ x ∈ A ∧ y ∈ A
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := fun h => h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
      trans := by
        intro x y z hxy hyz
        rcases hxy with rfl | ⟨hx, hy⟩
        · exact hyz
        · rcases hyz with rfl | ⟨_, hz⟩
          · exact Or.inr ⟨hx, hy⟩
          · exact Or.inr ⟨hx, hz⟩ }

abbrev Collapsed (A : Set Y) := Quotient (collapseSetoid A)

def collapseMap (A : Set Y) : C(Y, Collapsed A) :=
  ⟨Quotient.mk _, continuous_quotient_mk'⟩

theorem collapseMap_eq_iff (A : Set Y) (x y : Y) :
    collapseMap A x = collapseMap A y ↔ x = y ∨ x ∈ A ∧ y ∈ A :=
  Quotient.eq

theorem exists_collapse_homotopyEquiv (A : Set Y)
    (hHEP : TauCeti.HasHomotopyExtensionProperty A) [ContractibleSpace A] :
    ∃ e : Y ≃ₕ Collapsed A, e.toFun = collapseMap A := by
  obtain ⟨a, ⟨H⟩⟩ := id_nullhomotopic A
  let HA : C(I × A, Y) := (ContinuousMap.subtypeVal A).comp H.toContinuousMap
  obtain ⟨G, hG0, hGA⟩ := hHEP.exists_extension (ContinuousMap.id Y) HA
    (fun x => congrArg Subtype.val (H.apply_zero x))
  have hG1 (x : A) : G (1, x) = a := by
    rw [hGA]
    exact congrArg Subtype.val (H.apply_one x)
  have hrel : ∀ x y, (collapseSetoid A).r x y → G (1, x) = G (1, y) := by
    intro x y hxy
    rcases hxy with rfl | ⟨hx, hy⟩
    · rfl
    · exact (hG1 ⟨x, hx⟩).trans (hG1 ⟨y, hy⟩).symm
  let r : C(Collapsed A, Y) :=
    ⟨Quotient.lift (fun x => G (1, x)) hrel,
      Continuous.quotient_lift (G.continuous.comp (continuous_const.prodMk continuous_id)) _⟩
  have hqrel (t : I) : ∀ x y, (collapseSetoid A).r x y →
      collapseMap A (G (t, x)) = collapseMap A (G (t, y)) := by
    intro x y hxy
    rcases hxy with rfl | ⟨hx, hy⟩
    · rfl
    · apply Quotient.sound
      right
      exact ⟨by rw [hGA t ⟨x, hx⟩]; exact (H (t, ⟨x, hx⟩)).2,
        by rw [hGA t ⟨y, hy⟩]; exact (H (t, ⟨y, hy⟩)).2⟩
  let Q : I × Collapsed A → Collapsed A := fun p =>
    Quotient.lift (fun x => collapseMap A (G (p.1, x))) (hqrel p.1) p.2
  have hQ : Continuous Q := by
    apply isQuotientMap_quotient_mk'.continuous_lift_prod_right
    exact (collapseMap A).continuous.comp G.continuous
  let HY : (ContinuousMap.id Y).Homotopy (r.comp (collapseMap A)) :=
    { toContinuousMap := G
      map_zero_left := hG0
      map_one_left := fun _ => rfl }
  let HQ : (ContinuousMap.id (Collapsed A)).Homotopy ((collapseMap A).comp r) :=
    { toFun := Q
      continuous_toFun := hQ
      map_zero_left := by
        intro x
        induction x using Quotient.inductionOn with
        | _ x => exact congrArg (collapseMap A) (hG0 x)
      map_one_left := by
        intro x
        induction x using Quotient.inductionOn with
        | _ x => rfl }
  refine ⟨{ toFun := collapseMap A
            invFun := r
            left_inv := ⟨HY.symm⟩
            right_inv := ⟨HQ.symm⟩ }, rfl⟩

variable [T2Space Y] [Topology.CWComplex (Set.univ : Set Y)]

theorem cw_subcomplex_hasHEP
    (A : Topology.RelCWComplex.Subcomplex (Set.univ : Set Y)) :
    TauCeti.HasHomotopyExtensionProperty (A : Set Y) := by
  letI : Topology.RelCWComplex (Set.univ : Set Y) (A : Set Y) := A.relCWComplex
  have h : TauCeti.HasHomotopyExtensionProperty
      (Subtype.val ⁻¹' (A : Set Y) : Set (Set.univ : Set Y)) :=
    TauCeti.hasHomotopyExtensionProperty_base (X := Y)
      (C := (Set.univ : Set Y)) (D := (A : Set Y))
  have he : TauCeti.HasHomotopyExtensionProperty
      ((Homeomorph.Set.univ Y) '' (Subtype.val ⁻¹' (A : Set Y) : Set (Set.univ : Set Y))) :=
    TauCeti.HasHomotopyExtensionProperty.image
    (X := (Set.univ : Set Y)) (X' := Y)
    (A := (Subtype.val ⁻¹' (A : Set Y) : Set (Set.univ : Set Y)))
    h (Homeomorph.Set.univ Y)
  have hset : (Homeomorph.Set.univ Y) ''
      (Subtype.val ⁻¹' (A : Set Y) : Set (Set.univ : Set Y)) = A := by
    ext x
    simp
  rwa [hset] at he

/-- The usual finite CW case is included; the proof in fact does not need
finiteness. Contractibility entails the required nonemptiness of A. -/
theorem cw_collapse_homotopyEquiv
    (A : Topology.RelCWComplex.Subcomplex (Set.univ : Set Y))
    [ContractibleSpace (A : Set Y)] :
    ∃ e : Y ≃ₕ Collapsed (A : Set Y), e.toFun = collapseMap (A : Set Y) :=
  exists_collapse_homotopyEquiv (A : Set Y) (cw_subcomplex_hasHEP A)

end
end MathGauge.GP001
