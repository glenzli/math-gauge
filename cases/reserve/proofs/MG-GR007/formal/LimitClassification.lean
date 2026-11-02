import SectionCoordinates
import CoherentTransport

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation MathGauge.RepresentationTower
namespace MathGauge.GR007.LimitClassification
open SectionCoordinates
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


/-- All actual compatible section families correspond bijectively to sections
of the actual compatible-sequence limit representation. -/
def familyEquiv : MathGauge.SectionTransport.CoherentSections σ ρB b q ≃
    Sections (record ρB σ b q) where
  toFun s := ⟨assemble ρB σ b s.val s.property.2,
    record_assemble ρB σ b q s.val s.property.2 s.property.1⟩
  invFun s := ⟨fun n => (coordinate ρB b n).comp s.val,by
    constructor
    · intro n; apply IntertwiningMap.ext; apply LinearMap.ext; intro c
      change q n ((s.val c).val n)=c
      rw [record_coordinate ρB σ b q hq]
      exact congrArg (fun f => f c) s.property
    · intro n; apply IntertwiningMap.ext; apply LinearMap.ext; intro c
      exact (s.val c).property n⟩
  left_inv s := rfl
  right_inv s := rfl

/-- Classification with the original kernel inclusion and actual Hom(C,A∞). -/
def parameterEquiv (s : Sections (record ρB σ b q)) :
    (σ.IntertwiningMap (limitRep ρA a)) ≃ MathGauge.SectionTransport.CoherentSections σ ρB b q :=
  (coordinates (mapLimit ρA ρB a b i hb) (record ρB σ b q)
    (mapLimit_injective ρA ρB a b i hb hi)
    (mapLimit_exact ρA ρB σ a b i q hb hq hi hex) s).trans (familyEquiv ρB σ b q hq).symm

include i hb hq hi hex in
theorem unique_family_iff (s : Sections (record ρB σ b q)) :
    (∃! x : MathGauge.SectionTransport.CoherentSections σ ρB b q,True) ↔
      ∀ u : σ.IntertwiningMap (limitRep ρA a),u=0 := by
  let e := parameterEquiv ρA ρB σ a b i q hb hq hi hex s
  constructor
  · rintro ⟨x,_,hx⟩ u
    exact e.injective ((hx (e u) trivial).trans (hx (e 0) trivial).symm)
  · intro hz
    refine ⟨e 0,trivial,?_⟩
    intro x _
    obtain ⟨u,rfl⟩ := e.surjective x
    rw [hz u]

end MathGauge.GR007.LimitClassification
