import SectionCoordinates
import ChartStability

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation
namespace MathGauge.GR007.SectionTail
open SectionCoordinates EventualTower
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
variable (hb : ∀ n, (b n).comp (i (n+1))=(i n).comp (a n))
variable (hq : ∀ n, (q n).comp (b n)=q (n+1))
variable (hi : ∀ n, Function.Injective (i n))
variable (he : ∀ n, LinearMap.range (i n).toLinearMap=LinearMap.ker (q n).toLinearMap)
variable (base : ∀ n, Sections (q n))

include a i hb hi he base in
theorem actual_stability [∀ n, FiniteDimensional k (σ.IntertwiningMap (ρA n))] (n : ℕ) :
    (∃ N, ∃ hN : n ≤ N, ∀ m, ∀ hm : N ≤ m,
      Set.range (down (X := fun n => Sections (q n)) (transition ρB σ b q hq) n N hN)=
      Set.range (down (X := fun n => Sections (q n)) (transition ρB σ b q hq) n m (hN.trans hm))) ∧
    (∀ x∈ChartStability.stable (X := fun n => Sections (q n)) (transition ρB σ b q hq) n,
      ∃ y∈ChartStability.stable (X := fun n => Sections (q n)) (transition ρB σ b q hq) (n+1),transition ρB σ b q hq n y=x) := by
  let e := fun n => coordinates (i n) (q n) (hi n) (he n) (base n)
  let L := linearTransition ρA σ a
  let d := displacement ρA ρB σ b i q hq hi he base
  have hf : ∀ n u,transition ρB σ b q hq n (e (n+1) u)=e n (AffineTower.step L d n u) :=
    transition_coordinates ρA ρB σ a b i q hb hq hi he base
  exact ⟨ChartStability.actual_images_stabilize e _ L d hf n,
    ChartStability.actual_stable_surjective e _ L d hf n⟩

variable (N : ℕ)
variable (hbij : ∀ n,N ≤ n → Function.Bijective (transition ρB σ b q hq n))

/-- Evaluation of the actual compatible section family. -/
def evalEquiv : Coherent (X := fun n => Sections (q n)) (transition ρB σ b q hq) ≃ Sections (q N) :=
  evaluationEquiv (X := fun n => Sections (q n)) (transition ρB σ b q hq) N hbij

def affineCombination (t : k) (n : ℕ) (s r : Sections (q n)) : Sections (q n) :=
  ⟨t • s.val+(1-t) • r.val,by
    apply IntertwiningMap.ext; apply LinearMap.ext; intro c
    change q n (t • s.val c+(1-t) • r.val c)=c
    have hs : q n (s.val c)=c := congrArg (fun f => f c) s.property
    have hr : q n (r.val c)=c := congrArg (fun f => f c) r.property
    rw [map_add,map_smul,map_smul,hs,hr,← add_smul]
    simp⟩

def familyCombination (t : k) (s r : Coherent (X := fun n => Sections (q n)) (transition ρB σ b q hq)) :
    Coherent (X := fun n => Sections (q n)) (transition ρB σ b q hq) :=
  ⟨fun n => affineCombination ρB σ q t n (s.val n) (r.val n),by
    intro n; apply Subtype.ext; apply IntertwiningMap.ext; apply LinearMap.ext; intro c
    have hs := congrArg (fun z : Sections (q n) => z.val c) (s.property n)
    have hr := congrArg (fun z : Sections (q n) => z.val c) (r.property n)
    change b n (t • (s.val (n+1)).val c+(1-t) • (r.val (n+1)).val c)=_
    rw [map_add,map_smul,map_smul]
    change t • (transition ρB σ b q hq n (s.val (n+1))).val c+
      (1-t) • (transition ρB σ b q hq n (r.val (n+1))).val c=_
    dsimp only at hs hr
    rw [hs,hr]
    rfl⟩

@[simp] theorem eval_affine (t : k) (s r : Coherent (X := fun n => Sections (q n)) (transition ρB σ b q hq)) :
    evalEquiv ρB σ b q hq N hbij (familyCombination ρB σ b q hq t s r)=
    affineCombination ρB σ q t N (evalEquiv ρB σ b q hq N hbij s)
      (evalEquiv ρB σ b q hq N hbij r) := rfl

/-- Ternary affine addition is needed over arbitrary fields: binary affine
combinations alone do not detect additive affine structure over F₂. -/
def ternary (n : ℕ) (s r t : Sections (q n)) : Sections (q n) :=
  ⟨s.val-r.val+t.val,by
    apply IntertwiningMap.ext; apply LinearMap.ext; intro c
    change q n (s.val c-r.val c+t.val c)=c
    have hs : q n (s.val c)=c := congrArg (fun f => f c) s.property
    have hr : q n (r.val c)=c := congrArg (fun f => f c) r.property
    have ht : q n (t.val c)=c := congrArg (fun f => f c) t.property
    rw [map_add,map_sub,hs,hr,ht,sub_self,zero_add]⟩

def familyTernary (s r t : Coherent (X := fun n => Sections (q n)) (transition ρB σ b q hq)) :
    Coherent (X := fun n => Sections (q n)) (transition ρB σ b q hq) :=
  ⟨fun n => ternary ρB σ q n (s.val n) (r.val n) (t.val n),by
    intro n; apply Subtype.ext; apply IntertwiningMap.ext; apply LinearMap.ext; intro c
    have hs := congrArg (fun z : Sections (q n) => z.val c) (s.property n)
    have hr := congrArg (fun z : Sections (q n) => z.val c) (r.property n)
    have ht := congrArg (fun z : Sections (q n) => z.val c) (t.property n)
    change b n ((s.val (n+1)).val c-(r.val (n+1)).val c+(t.val (n+1)).val c)=_
    rw [map_add,map_sub]
    change (transition ρB σ b q hq n (s.val (n+1))).val c-
      (transition ρB σ b q hq n (r.val (n+1))).val c+
      (transition ρB σ b q hq n (t.val (n+1))).val c=_
    dsimp only at hs hr ht
    rw [hs,hr,ht]
    rfl⟩

@[simp] theorem eval_ternary
    (s r t : Coherent (X := fun n => Sections (q n)) (transition ρB σ b q hq)) :
    evalEquiv ρB σ b q hq N hbij (familyTernary ρB σ b q hq s r t)=
    ternary ρB σ q N (evalEquiv ρB σ b q hq N hbij s)
      (evalEquiv ρB σ b q hq N hbij r) (evalEquiv ρB σ b q hq N hbij t) := rfl

theorem inverse_eval_ternary (s r t : Sections (q N)) :
    (evalEquiv ρB σ b q hq N hbij).symm (ternary ρB σ q N s r t)=
    familyTernary ρB σ b q hq ((evalEquiv ρB σ b q hq N hbij).symm s)
      ((evalEquiv ρB σ b q hq N hbij).symm r)
      ((evalEquiv ρB σ b q hq N hbij).symm t) := by
  apply (evalEquiv ρB σ b q hq N hbij).injective
  simp only [Equiv.apply_symm_apply,eval_ternary]

/-- The inverse evaluation preserves the actual pointwise affine operation. -/
theorem inverse_eval_affine (t : k) (s r : Sections (q N)) :
    (evalEquiv ρB σ b q hq N hbij).symm (affineCombination ρB σ q t N s r)=
    familyCombination ρB σ b q hq t ((evalEquiv ρB σ b q hq N hbij).symm s)
      ((evalEquiv ρB σ b q hq N hbij).symm r) := by
  apply (evalEquiv ρB σ b q hq N hbij).injective
  simp only [Equiv.apply_symm_apply,eval_affine]

/-- The direction space is exactly W_N, with no finite-dimensional assumption. -/
def parameterChart : (σ.IntertwiningMap (ρA N)) ≃ Coherent (X := fun n => Sections (q n)) (transition ρB σ b q hq) :=
  (coordinates (i N) (q N) (hi N) (he N) (base N)).trans
    (evalEquiv ρB σ b q hq N hbij).symm

theorem parameterChart_affine (t : k) (u v : σ.IntertwiningMap (ρA N)) :
    parameterChart ρA ρB σ b i q hq hi he base N hbij (t • u+(1-t) • v)=
    familyCombination ρB σ b q hq t
      (parameterChart ρA ρB σ b i q hq hi he base N hbij u)
      (parameterChart ρA ρB σ b i q hq hi he base N hbij v) := by
  apply (evalEquiv ρB σ b q hq N hbij).injective
  change (evalEquiv ρB σ b q hq N hbij)
    ((evalEquiv ρB σ b q hq N hbij).symm _) = _
  simp only [Equiv.apply_symm_apply,eval_affine]
  change (coordinates (i N) (q N) (hi N) (he N) (base N) (t • u+(1-t) • v)) =
    affineCombination ρB σ q t N
      ((evalEquiv ρB σ b q hq N hbij) ((evalEquiv ρB σ b q hq N hbij).symm _))
      ((evalEquiv ρB σ b q hq N hbij) ((evalEquiv ρB σ b q hq N hbij).symm _))
  simp only [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact coordinates_affine (i N) (q N) (hi N) (he N) (base N) t u v

theorem parameterChart_ternary (u v w : σ.IntertwiningMap (ρA N)) :
    parameterChart ρA ρB σ b i q hq hi he base N hbij (u-v+w)=
    familyTernary ρB σ b q hq
      (parameterChart ρA ρB σ b i q hq hi he base N hbij u)
      (parameterChart ρA ρB σ b i q hq hi he base N hbij v)
      (parameterChart ρA ρB σ b i q hq hi he base N hbij w) := by
  apply (evalEquiv ρB σ b q hq N hbij).injective
  change (evalEquiv ρB σ b q hq N hbij)
    ((evalEquiv ρB σ b q hq N hbij).symm _) = _
  simp only [Equiv.apply_symm_apply,eval_ternary]
  change (coordinates (i N) (q N) (hi N) (he N) (base N) (u-v+w)) =
    ternary ρB σ q N
      ((evalEquiv ρB σ b q hq N hbij) ((evalEquiv ρB σ b q hq N hbij).symm _))
      ((evalEquiv ρB σ b q hq N hbij) ((evalEquiv ρB σ b q hq N hbij).symm _))
      ((evalEquiv ρB σ b q hq N hbij) ((evalEquiv ρB σ b q hq N hbij).symm _))
  simp only [Equiv.apply_symm_apply]
  apply Subtype.ext
  exact coordinates_ternary (i N) (q N) (hi N) (he N) (base N) u v w

include i hi he base hbij in
theorem unique_iff_direction_zero :
    (∃! x : Coherent (X := fun n => Sections (q n)) (transition ρB σ b q hq),True) ↔
      ∀ u : σ.IntertwiningMap (ρA N),u=0 := by
  let e := parameterChart ρA ρB σ b i q hq hi he base N hbij
  constructor
  · rintro ⟨x,_,hx⟩ u
    exact e.injective ((hx (e u) trivial).trans (hx (e 0) trivial).symm)
  · intro hz
    refine ⟨e 0,trivial,?_⟩
    intro x _
    obtain ⟨u,rfl⟩ := e.surjective x
    rw [hz u]

end MathGauge.GR007.SectionTail
