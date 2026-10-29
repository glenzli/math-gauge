import RepresentationTower
import SplitRepresentation

noncomputable section
open Representation
namespace MathGauge.RepresentationTower
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

def coordinate (n : ℕ) : (limitRep ρB b).IntertwiningMap (ρB n) where
  toLinearMap :=
    { toFun := fun x => x.val n
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  isIntertwining' _ := rfl

def mapLimit : (limitRep ρA a).IntertwiningMap (limitRep ρB b) where
  toLinearMap :=
    { toFun := fun x => ⟨fun n => i n (x.val n), by
        intro n
        calc
          b n (i (n+1) (x.val (n+1))) = i n (a n (x.val (n+1))) :=
            congrArg (fun f : (ρA (n+1)).IntertwiningMap (ρB n) => f (x.val (n+1))) (hb n)
          _ = i n (x.val n) := congrArg (i n) (x.property n)⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  isIntertwining' := by
    intro g; apply LinearMap.ext; intro x; apply Subtype.ext; funext n
    exact IntertwiningMap.isIntertwining (ρA n) (ρB n) (i n) g (x.val n)

include hi in
theorem mapLimit_injective : Function.Injective (mapLimit ρA ρB a b i hb) := by
  intro x y h
  apply Subtype.ext; funext n; apply hi n
  exact congrArg (fun t : limit ρB b => t.val n) h

include hi hex hq in
theorem mapLimit_exact :
    LinearMap.range (mapLimit ρA ρB a b i hb).toLinearMap =
      LinearMap.ker (record ρB σ b q).toLinearMap := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change q 0 (i 0 (y.val 0))=0
    exact MathGauge.SplitRepresentation.qi (i 0) (q 0) (hex 0) _
  · intro hx
    change record ρB σ b q x=0 at hx
    have hn : ∀ n, q n (x.val n)=0 := fun n =>
      (record_coordinate ρB σ b q hq x n).trans hx
    have hl : ∀ n, ∃ y, i n y=x.val n := by
      intro n
      have h : x.val n ∈ LinearMap.ker (q n).toLinearMap := hn n
      rw [← hex n] at h
      exact h
    choose y hy using hl
    have hc : ∀ n, a n (y (n+1))=y n := by
      intro n; apply hi n
      calc
        i n (a n (y (n+1))) = b n (i (n+1) (y (n+1))) :=
          (congrArg (fun f : (ρA (n+1)).IntertwiningMap (ρB n) => f (y (n+1))) (hb n)).symm
        _ = b n (x.val (n+1)) := congrArg (b n) (hy (n+1))
        _ = x.val n := x.property n
        _ = i n (y n) := (hy n).symm
    exact ⟨⟨y,hc⟩,Subtype.ext (funext hy)⟩

include hi hex hq

/-- A genuine coherent choice exists, then its original inclusion and projection give an equivariant decomposition. -/
theorem full_split [FiniteDimensional k C] [∀ n, FiniteDimensional k (B n)]
    (hs : ∀ n, ∃ s : σ.IntertwiningMap (ρB n), (q n).comp s=IntertwiningMap.id σ) :
    ∃ s : ∀ n, σ.IntertwiningMap (ρB n),
      (∀ n, (q n).comp (s n)=IntertwiningMap.id σ) ∧
      (∀ n, (b n).comp (s (n+1))=s n) ∧
      ∃ e : Representation.Equiv ((limitRep ρA a).prod σ) (limitRep ρB b),
        (∀ x, e (x,0)=mapLimit ρA ρB a b i hb x) ∧
        (∀ x c, record ρB σ b q (e (x,c))=c) := by
  obtain ⟨s,hsq,hsc⟩ := coherent_sections ρB σ b q hq hs
  let sl := assemble ρB σ b s hsc
  have hsl : (record ρB σ b q).comp sl=IntertwiningMap.id σ :=
    record_assemble ρB σ b q s hsc hsq
  let e := MathGauge.SplitRepresentation.splitEquiv (mapLimit ρA ρB a b i hb)
    (record ρB σ b q) (mapLimit_injective ρA ρB a b i hb hi)
    (mapLimit_exact ρA ρB σ a b i q hb hq hi hex) sl hsl
  refine ⟨s,hsq,hsc,e,?_,?_⟩
  · intro x; exact MathGauge.SplitRepresentation.split_inclusion _ _ _ _ _ _ x
  · intro x c; exact MathGauge.SplitRepresentation.split_projection _ _ _ _ _ _ x c

/-- All coherent sections, expressed on the limit, form the exact torsor in the reference. -/
theorem all_limit_sections (s t : σ.IntertwiningMap (limitRep ρB b))
    (hs : (record ρB σ b q).comp s=IntertwiningMap.id σ) :
    (record ρB σ b q).comp t=IntertwiningMap.id σ ↔
      ∃! u : σ.IntertwiningMap (limitRep ρA a),
        t=s+(mapLimit ρA ρB a b i hb).comp u := by
  exact MathGauge.SplitRepresentation.sections_classified
    (mapLimit ρA ρB a b i hb) (record ρB σ b q)
    (mapLimit_injective ρA ρB a b i hb hi)
    (mapLimit_exact ρA ρB σ a b i q hb hq hi hex) s t hs

/-- Coordinate extraction and assembly are mutual inverses, so the limit classification misses no families. -/
theorem assemble_coordinates (s : σ.IntertwiningMap (limitRep ρB b)) :
    ∃ h : ∀ n, (b n).comp ((coordinate ρB b (n+1)).comp s) =
      (coordinate ρB b n).comp s,
      assemble ρB σ b (fun n => (coordinate ρB b n).comp s) h=s := by
  have h : ∀ n, (b n).comp ((coordinate ρB b (n+1)).comp s) =
      (coordinate ρB b n).comp s := by
    intro n; apply IntertwiningMap.ext; apply LinearMap.ext; intro c
    exact (s c).property n
  exact ⟨h,rfl⟩

end MathGauge.RepresentationTower
