import SplittingClassification

noncomputable section
namespace MathGauge.IdempotentSections
open MathGauge.SplittingClassification
universe u v
variable {R : Type u} [CommRing R]
variable {B : Type v} [AddCommGroup B] [Module R B]

abbrev ideal (e : R) : Ideal R := Ideal.span {e}
abbrev Quot (e : R) := R ⧸ (ideal e : Submodule R R)

def raw (e : R) (b : B) : R →ₗ[R] B :=
  (LinearMap.toSpanSingleton R B b).comp (LinearMap.mulRight R (1-e))

theorem raw_kills (e : R) (he : e*e=e) (b : B) : (ideal e : Submodule R R) ≤ (raw e b).ker := by
  intro r hr
  obtain ⟨a,rfl⟩ := Ideal.mem_span_singleton.mp hr
  change ((e*a)*(1-e)) • b=0
  have hz : (e*a)*(1-e)=0 := by
    calc (e*a)*(1-e)=(e-e*e)*a := by ring
      _=0 := by rw [he,sub_self,zero_mul]
  rw [hz,zero_smul]

def idempotentSection (e : R) (he : e*e=e) (b : B) : Quot e →ₗ[R] B :=
  (ideal e).liftQ (raw e b) (raw_kills e he b)

@[simp] theorem section_mk (e : R) (he : e*e=e) (b : B) (r : R) :
    idempotentSection e he b ((ideal e).mkQ r)=(r*(1-e)) • b := rfl

theorem section_right_inverse (e : R) (he : e*e=e) (q : B →ₗ[R] Quot e)
    (b : B) (hb : q b=(ideal e).mkQ 1) : q.comp (idempotentSection e he b)=LinearMap.id := by
  apply LinearMap.ext
  intro c
  induction c using Submodule.Quotient.induction_on (ideal e) with
  | H r =>
    change q (idempotentSection e he b ((ideal e).mkQ r))=(ideal e).mkQ r
    rw [section_mk,map_smul,hb,← map_smul]
    change (ideal e).mkQ ((r*(1-e))*1)=(ideal e).mkQ r
    rw [mul_one,mul_sub,mul_one,map_sub]
    have hz : (ideal e).mkQ (r*e)=0 :=
      (Submodule.Quotient.mk_eq_zero _).2 ((ideal e).mul_mem_left r (Ideal.subset_span (by simp)))
    rw [hz,sub_zero]

def explicitSplit (e : R) (he : e*e=e) (q : B →ₗ[R] Quot e)
    (b : B) (hb : q b=(ideal e).mkQ 1) : (q.ker × Quot e) ≃ₗ[R] B :=
  kernelSplit q ⟨idempotentSection e he b,section_right_inverse e he q b hb⟩

theorem section_exists (e : R) (he : e*e=e) (q : B →ₗ[R] Quot e)
    (hq : Function.Surjective q) : Nonempty (Sections q) := by
  obtain ⟨b,hb⟩ := hq ((ideal e).mkQ 1)
  exact ⟨⟨idempotentSection e he b,section_right_inverse e he q b hb⟩⟩

/-- A splitting of the actual quotient map supplies the idempotent generator;
no finite-generation assumption is needed in this direction. -/
theorem generator_of_quotient_section (I : Ideal R)
    (s : R ⧸ (I : Submodule R R) →ₗ[R] R) (hs : I.mkQ.comp s=LinearMap.id) :
    ∃ e : R,e*e=e ∧ I=Ideal.span {e} := by
  let a := s (I.mkQ 1)
  have ha : I.mkQ a=I.mkQ 1 := LinearMap.congr_fun hs (I.mkQ 1)
  have hkill (r : R) (hr : r∈I) : r*a=0 := by
    change r • s (I.mkQ 1)=0
    rw [← map_smul,← map_smul]
    change s (I.mkQ (r*1))=0
    have hq : I.mkQ r=0 := (Submodule.Quotient.mk_eq_zero _).2 hr
    rw [mul_one,hq,map_zero]
  have heI : 1-a∈I := by
    apply (Submodule.Quotient.mk_eq_zero _).1
    change I.mkQ (1-a)=0
    rw [map_sub,ha,sub_self]
  refine ⟨1-a,?_,?_⟩
  · have hk := hkill (1-a) heI
    calc (1-a)*(1-a)=(1-a)-(1-a)*a := by ring
      _=1-a := by rw [hk,sub_zero]
  · apply le_antisymm
    · intro r hr
      apply Ideal.mem_span_singleton.mpr
      refine ⟨r,?_⟩
      have hk := hkill r hr
      calc r=r-r*a := by rw [hk,sub_zero]
        _=(1-a)*r := by ring
    · exact Ideal.span_le.2 (by intro r hr;simpa using (show r=1-a from hr) ▸ heI)

/-- The exact finite-presentation hypothesis is derived from the finitely
generated ideal; it is not inferred merely from a cyclic quotient. -/
theorem finite_ideal_local_sections (I : Ideal R) (hI : I.FG)
    [Module.Free R B] [Module.Finite R B]
    (q : B →ₗ[R] R ⧸ (I : Submodule R R))
    (hlocal : ∀ (p : Ideal R) [p.IsPrime],∃ s :
      LocalizedModule p.primeCompl (R ⧸ (I : Submodule R R)) →ₗ[Localization.AtPrime p]
        LocalizedModule p.primeCompl B,
      (LocalizedModule.map p.primeCompl q).comp s=LinearMap.id) :
    (∃ e : R,e*e=e ∧ I=Ideal.span {e}) ∧ Nonempty (Sections q) := by
  letI : Module.FinitePresentation R (R ⧸ (I : Submodule R R)) :=
    Module.finitePresentation_of_free_of_surjective I.mkQ I.mkQ_surjective (by simpa using hI)
  obtain ⟨s,hs⟩ := q.split_surjective_of_localization_maximal (fun p hp => by
    letI := hp
    exact hlocal p)
  letI : Module.Projective R (R ⧸ (I : Submodule R R)) := Module.Projective.of_split s q hs
  obtain ⟨s',hs'⟩ := Module.projective_lifting_property I.mkQ LinearMap.id I.mkQ_surjective
  exact ⟨generator_of_quotient_section I s' hs',⟨⟨s,hs⟩⟩⟩

theorem finite_support_idempotent :
    MathGauge.LocalSplitting.finiteSupportIdeal * MathGauge.LocalSplitting.finiteSupportIdeal=
      MathGauge.LocalSplitting.finiteSupportIdeal := by
  apply le_antisymm Ideal.mul_le_left
  intro a ha
  rw [← MathGauge.LocalSplitting.boolean_identity a]
  exact Ideal.mul_mem_mul ha ha

theorem idempotent_not_split :
    MathGauge.LocalSplitting.finiteSupportIdeal * MathGauge.LocalSplitting.finiteSupportIdeal=
      MathGauge.LocalSplitting.finiteSupportIdeal ∧
    MathGauge.LocalSplitting.q 1≠0 ∧
    ¬∃ s : MathGauge.LocalSplitting.C →ₗ[MathGauge.LocalSplitting.R] MathGauge.LocalSplitting.R,
      MathGauge.LocalSplitting.q.comp s=LinearMap.id :=
  ⟨finite_support_idempotent,MathGauge.LocalSplitting.q_one_ne_zero,
    MathGauge.LocalSplitting.no_global_section⟩

end MathGauge.IdempotentSections
