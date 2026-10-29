import ProfiniteOrbitLocal
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Data.ZMod.Basic

noncomputable section
open CategoryTheory Opposite
namespace MathGauge.Descent

abbrev RealProbe : ProfSheaf.{0,0} := prof_probe_sheaf.{0,0} ℝ

def real_translation : SpaceAction (Multiplicative ℝ) ℝ where
  act a := Homeomorph.addLeft a.toAdd
  one x := zero_add x
  mul a b x := add_assoc a.toAdd b.toAdd x

abbrev real_translation_action : PAction.{1,0,0,0} (Γ := Multiplicative ℝ) RealProbe.obj :=
  SpaceAction.probe_action.{0,0,0} real_translation
abbrev RealOrbit : ProfSheaf.{0,0} := real_translation_action.quotient_sheaf ProfSite
abbrev real_q := real_translation_action.quotient_projection ProfSite

def real_neg : RealProbe ⟶ RealProbe := ⟨{
  app U f := ⟨⟨fun x => -(f.down x),f.down.continuous.neg⟩⟩
  naturality := by intro U V f; rfl }⟩

theorem real_neg_q_invariant :
    real_translation_action.Invariant (real_neg.hom ≫ real_q) := by
  intro a
  ext U f
  have h := congrArg (fun η => η.app U (real_neg.hom.app U f))
    (real_translation_action.quotient_invariant ProfSite (Multiplicative.ofAdd (-a.toAdd)))
  have he : real_neg.hom.app U ((real_translation_action.act a).app U f) =
      (real_translation_action.act (Multiplicative.ofAdd (-a.toAdd))).app U
        (real_neg.hom.app U f) := by
    apply ULift.ext
    ext x
    simp [real_neg,real_translation,SpaceAction.probe_action,add_comm]
  change real_q.app U (real_neg.hom.app U ((real_translation_action.act a).app U f)) = _
  rw [he]
  exact h

def real_orbit_neg : RealOrbit ⟶ RealOrbit :=
  real_translation_action.quotient_lift ProfSite _ (real_neg.hom ≫ real_q) real_neg_q_invariant

theorem real_orbit_neg_fac : real_q ≫ real_orbit_neg.hom = real_neg.hom ≫ real_q :=
  real_translation_action.quotient_lift_fac ProfSite _ _ _

theorem real_orbit_neg_involution : real_orbit_neg ≫ real_orbit_neg = 𝟙 _ := by
  apply Sheaf.hom_ext
  apply real_translation_action.quotient_hom_ext ProfSite _
  change real_q ≫ (real_orbit_neg.hom ≫ real_orbit_neg.hom) = real_q ≫ 𝟙 _
  rw [← Category.assoc,real_orbit_neg_fac,Category.assoc,real_orbit_neg_fac]
  ext U f
  change real_q.app U (real_neg.hom.app U (real_neg.hom.app U f)) = real_q.app U f
  apply congrArg (real_q.app U)
  apply ULift.ext
  ext x
  simp [real_neg]

instance real_orbit_point_subsingleton : Subsingleton (RealOrbit.obj.obj (op ProfPoint)) := by
  constructor
  intro x y
  obtain ⟨f,rfl⟩ := prof_point_locally_surjective.{0,0} real_q x
  obtain ⟨g,rfl⟩ := prof_point_locally_surjective.{0,0} real_q y
  apply (quotient_point_eq_iff real_translation_action f g).mpr
  refine ⟨Multiplicative.ofAdd (g.down PUnit.unit - f.down PUnit.unit),?_⟩
  apply ULift.ext
  ext t
  change g.down PUnit.unit - f.down PUnit.unit + f.down t = g.down t
  have ht : t = PUnit.unit := Subsingleton.elim _ _
  subst t
  simp

abbrev CantorProbe : Profinite.{0} := Profinite.of (ℕ → Bool)

def cantor_real : C(CantorProbe,ℝ) :=
  ⟨fun x => (cantorSetHomeomorphNatToBool.symm x).val,
    continuous_subtype_val.comp cantorSetHomeomorphNatToBool.symm.continuous⟩

theorem cantor_real_injective : Function.Injective cantor_real :=
  Subtype.val_injective.comp cantorSetHomeomorphNatToBool.symm.injective

theorem real_q_eq_finite_difference (S : Profinite.{0}) (f g : C(S,ℝ))
    (heq : real_q.app (op S) ⟨f⟩ = real_q.app (op S) ⟨g⟩) :
    (Set.range (fun s => g s - f s)).Finite := by
  obtain ⟨ι,hι,V,v,hv,ha⟩ :=
    (quotient_eq_iff_finite_cover real_translation_action S ⟨f⟩ ⟨g⟩).mp heq
  let a : ι → Multiplicative ℝ := fun i => Classical.choose (ha i)
  apply (Set.finite_range (fun i => (a i).toAdd)).subset
  rintro z ⟨s,rfl⟩
  obtain ⟨i,t,ht⟩ := hv s
  refine ⟨i,?_⟩
  have h := congrArg (fun w => w.down t) (Classical.choose_spec (ha i))
  change (a i).toAdd + f (v i t) = g (v i t) at h
  rw [ht] at h
  linarith

theorem cantor_q_ne_zero : real_q.app (op CantorProbe) ⟨cantor_real⟩ ≠
    real_q.app (op CantorProbe) ⟨ContinuousMap.const _ 0⟩ := by
  intro h
  have hf := real_q_eq_finite_difference CantorProbe cantor_real (ContinuousMap.const _ 0) h
  apply (Set.infinite_range_of_injective (f := fun s => (0:ℝ) - cantor_real s) ?_) hf
  intro s t he
  apply cantor_real_injective
  linarith

theorem cantor_q_neg_ne : real_orbit_neg.hom.app (op CantorProbe)
    (real_q.app (op CantorProbe) ⟨cantor_real⟩) ≠
      real_q.app (op CantorProbe) ⟨cantor_real⟩ := by
  intro h
  have fac := congrArg (fun η => η.app (op CantorProbe) ⟨cantor_real⟩) real_orbit_neg_fac
  change real_orbit_neg.hom.app (op CantorProbe) (real_q.app _ ⟨cantor_real⟩) =
    real_q.app _ (real_neg.hom.app _ ⟨cantor_real⟩) at fac
  have heq := fac.symm.trans h
  have hf := real_q_eq_finite_difference CantorProbe
    (real_neg.hom.app _ ⟨cantor_real⟩).down cantor_real heq
  apply (Set.infinite_range_of_injective (f := fun s =>
    cantor_real s - (real_neg.hom.app _ ⟨cantor_real⟩).down s) ?_) hf
  intro s t he
  apply cantor_real_injective
  change cantor_real s - -cantor_real s = cantor_real t - -cantor_real t at he
  linarith

abbrev TwoGroup := Multiplicative (ZMod 2)

def involution_action (F : ProfSheaf.{0,0}) (n : F ⟶ F) (hn : n ≫ n = 𝟙 _) :
    PAction.{1,0,0,0} (Γ := TwoGroup) F.obj where
  act a := if a.toAdd.val = 0 then 𝟙 _ else n.hom
  one := by rfl
  mul a b := by
    have h : n.hom ≫ n.hom = 𝟙 _ := congrArg (fun η => η.hom) hn
    change ZMod 2 at a b
    change (if (a + b).val = 0 then 𝟙 _ else n.hom) =
      (if b.val = 0 then 𝟙 _ else n.hom) ≫ (if a.val = 0 then 𝟙 _ else n.hom)
    fin_cases a <;> fin_cases b
    · exact (Category.id_comp _).symm
    · exact (Category.comp_id _).symm
    · exact (Category.id_comp _).symm
    · exact h.symm

def point_trivial_action : SpaceAction TwoGroup PUnit where
  act _ := Homeomorph.refl _
  one _ := rfl
  mul _ _ _ := rfl

def invisible_projection : RealOrbit ⟶ prof_probe_sheaf.{0,0} PUnit := ⟨{
  app _ _ := ⟨ContinuousMap.const _ PUnit.unit⟩
  naturality := by intro U V f; rfl }⟩

def invisible_record : EquivariantOver (SpaceAction.probe_action.{0,0,0} point_trivial_action) where
  sheaf := RealOrbit
  projection := invisible_projection
  action := involution_action RealOrbit real_orbit_neg real_orbit_neg_involution
  equivariant _ := rfl

theorem invisible_record_pointwise_trivial (a : TwoGroup)
    (e : RealOrbit.obj.obj (op ProfPoint)) :
    (invisible_record.action.act a).app (op ProfPoint) e = e :=
  @Subsingleton.elim (RealOrbit.obj.obj (op ProfPoint)) real_orbit_point_subsingleton _ _

theorem invisible_record_not_stabilizer_trivial : ¬invisible_record.StabilizerTrivial := by
  intro h
  have hfix := h (op CantorProbe) (real_q.app _ ⟨cantor_real⟩)
    (Multiplicative.ofAdd (1 : ZMod 2)) rfl
  apply cantor_q_neg_ne
  simpa [invisible_record,involution_action] using hfix

/-- A concrete counterexample to testing only ordinary singleton sections. -/
theorem invisible_record_not_realizable : ¬invisible_record.Realizable := by
  rw [invisible_record.realizable_iff_stabilizer_trivial]
  exact invisible_record_not_stabilizer_trivial

end MathGauge.Descent
