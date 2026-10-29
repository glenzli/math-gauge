import SectionCoordinates
import SplitClassification

noncomputable section
open Representation MathGauge.RepresentationTower
namespace MathGauge.GR007.FiniteParameters
universe u v w
variable {k : Type u} [Field k] {G : Type v} [Monoid G]
variable {A B : ℕ → Type w} [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)]
variable [∀ n, Module k (A n)] [∀ n, Module k (B n)]
variable {C : Type w} [AddCommGroup C] [Module k C]
variable (ρA : ∀ n, Representation k G (A n)) (ρB : ∀ n, Representation k G (B n))
variable (σ : Representation k G C)
variable (a : ∀ n, (ρA (n+1)).IntertwiningMap (ρA n))
variable (b : ∀ n, (ρB (n+1)).IntertwiningMap (ρB n))
variable (i : ∀ n, (ρA n).IntertwiningMap (ρB n))
variable (q : ∀ n, (ρB n).IntertwiningMap σ)
variable (hb : ∀ n, (b n).comp (i (n+1)) = (i n).comp (a n))
variable (hq : ∀ n, (q n).comp (b n) = q (n+1))
variable (hi : ∀ n, Function.Injective (i n))
variable (hex : ∀ n, LinearMap.range (i n).toLinearMap=LinearMap.ker (q n).toLinearMap)

include hi hex hq

/-- The full decomposition uses finite parameter spaces, without finite ambient B. -/
theorem full_split_finite_parameters [∀ n, FiniteDimensional k (σ.IntertwiningMap (ρA n))]
    (hs : ∀ n, ∃ s : σ.IntertwiningMap (ρB n), (q n).comp s=IntertwiningMap.id σ) :
    ∃ s : ∀ n, σ.IntertwiningMap (ρB n),
      (∀ n, (q n).comp (s n)=IntertwiningMap.id σ) ∧
      (∀ n, (b n).comp (s (n+1))=s n) ∧
      ∃ e : Representation.Equiv ((limitRep ρA a).prod σ) (limitRep ρB b),
        (∀ x, e (x,0)=mapLimit ρA ρB a b i hb x) ∧
        (∀ x c, record ρB σ b q (e (x,c))=c) := by
  choose s hs using hs
  let base : ∀ n, MathGauge.GR007.SectionCoordinates.Sections (q n) := fun n => ⟨s n,hs n⟩
  obtain ⟨s,hsq,hsc⟩ := MathGauge.GR007.SectionCoordinates.coherent_sections_of_finite_parameters
    ρA ρB σ a b i q hb hq hi hex base
  let sl := assemble ρB σ b s hsc
  have hsl : (record ρB σ b q).comp sl=IntertwiningMap.id σ :=
    record_assemble ρB σ b q s hsc hsq
  let e := MathGauge.SplitRepresentation.splitEquiv (mapLimit ρA ρB a b i hb)
    (record ρB σ b q) (mapLimit_injective ρA ρB a b i hb hi)
    (mapLimit_exact ρA ρB σ a b i q hb hq hi hex) sl hsl
  refine ⟨s,hsq,hsc,e,?_,?_⟩
  · intro x; exact MathGauge.SplitRepresentation.split_inclusion _ _ _ _ _ _ x
  · intro x c; exact MathGauge.SplitRepresentation.split_projection _ _ _ _ _ _ x c

end MathGauge.GR007.FiniteParameters
