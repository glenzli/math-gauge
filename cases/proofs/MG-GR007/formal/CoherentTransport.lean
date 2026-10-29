import SectionTransport

noncomputable section
open Representation
namespace MathGauge.SectionTransport
universe u v w
variable {k : Type u} [Field k] {G : Type v} [Monoid G]
variable {C C' : Type w} [AddCommGroup C] [AddCommGroup C'] [Module k C] [Module k C']
variable (σ : Representation k G C) (σ' : Representation k G C')
variable {V V' : ℕ → Type w} [∀ n, AddCommGroup (V n)] [∀ n, AddCommGroup (V' n)]
variable [∀ n, Module k (V n)] [∀ n, Module k (V' n)]
variable (ρ : ∀ n, Representation k G (V n)) (ρ' : ∀ n, Representation k G (V' n))
variable (b : ∀ n, (ρ (n+1)).IntertwiningMap (ρ n))
variable (b' : ∀ n, (ρ' (n+1)).IntertwiningMap (ρ' n))
variable (q : ∀ n, (ρ n).IntertwiningMap σ) (q' : ∀ n, (ρ' n).IntertwiningMap σ')

def CoherentSections := {s : ∀ n, σ.IntertwiningMap (ρ n) //
  (∀ n, (q n).comp (s n)=IntertwiningMap.id σ) ∧ (∀ n, (b n).comp (s (n+1))=s n)}

variable (d : Representation.Equiv σ σ') (e : ∀ n, Representation.Equiv (ρ n) (ρ' n))
variable (hb : ∀ n, (b' n).comp (e (n+1)).toIntertwiningMap=(e n).toIntertwiningMap.comp (b n))
variable (hq : ∀ n, (q' n).comp (e n).toIntertwiningMap=d.toIntertwiningMap.comp (q n))

include hq in
theorem inverse_record : ∀ n,
    (q n).comp (e n).symm.toIntertwiningMap=d.symm.toIntertwiningMap.comp (q' n) := by
  intro n; apply IntertwiningMap.ext; apply LinearMap.ext; intro x
  apply d.toLinearEquiv.injective
  change d (q n ((e n).symm x))=d (d.symm (q' n x))
  rw [d.apply_symm_apply]
  have he := congrArg (fun f : (ρ n).IntertwiningMap σ' => f ((e n).symm x)) (hq n)
  simpa using he.symm

/-- Actual coherent section families, with their equations, are transported bijectively. -/
def coherentSectionsEquiv : CoherentSections σ ρ b q ≃ CoherentSections σ' ρ' b' q' where
  toFun s := ⟨fun n => homEquiv d (e n) (s.val n),
    (fun n => transport_section d (e n) (q n) (q' n) (hq n) (s.val n) (s.property.1 n)),
    transport_coherent ρ ρ' b b' e d hb s.val s.property.2⟩
  invFun s := ⟨fun n => homEquiv d.symm (e n).symm (s.val n),
    (fun n => transport_section d.symm (e n).symm (q' n) (q n)
      (inverse_record σ σ' ρ ρ' q q' d e hq n) (s.val n) (s.property.1 n)),
    transport_coherent ρ' ρ b' b (fun n => (e n).symm) d.symm
      (inverse_diagram ρ ρ' b b' e hb) s.val s.property.2⟩
  left_inv s := by
    apply Subtype.ext; funext n
    apply IntertwiningMap.ext; apply LinearMap.ext; intro x
    simp
  right_inv s := by
    apply Subtype.ext; funext n
    apply IntertwiningMap.ext; apply LinearMap.ext; intro x
    simp

/-- Differences transform linearly, so the same formula transports the translation space. -/
theorem transport_difference (s t : ∀ n, σ.IntertwiningMap (ρ n)) :
    (fun n => homEquiv d (e n) (t n-s n))=
      (fun n => homEquiv d (e n) (t n)-homEquiv d (e n) (s n)) := by
  funext n; exact map_sub _ _ _

end MathGauge.SectionTransport
