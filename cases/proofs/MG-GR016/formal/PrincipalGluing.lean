import IdempotentSections
import Mathlib.Algebra.Module.LocalizedModule.Away

noncomputable section
open Set Function
namespace MathGauge.PrincipalGluing
universe u v
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

abbrev Loc (f : R) (M : Type v) [AddCommGroup M] [Module R M] :=
  LocalizedModule (Submonoid.powers f) M
abbrev loc (f : R) : M →ₗ[R] Loc f M := LocalizedModule.mkLinearMap (Submonoid.powers f) M

theorem overlap_units_left (f g : R) :
    IsUnit (algebraMap R (Module.End R (Loc (f*g) M)) f) := by
  have h := IsLocalizedModule.map_units (loc (M := M) (f*g))
    (⟨f*g,1,by simp⟩ : Submonoid.powers (f*g))
  change IsUnit (algebraMap R (Module.End R (Loc (f*g) M)) (f*g)) at h
  rw [map_mul] at h
  exact (((Commute.all f g).map (algebraMap R (Module.End R (Loc (f*g) M)))).isUnit_mul_iff.mp h).1

theorem overlap_units_right (f g : R) :
    IsUnit (algebraMap R (Module.End R (Loc (f*g) M)) g) := by
  have h := IsLocalizedModule.map_units (loc (M := M) (f*g))
    (⟨f*g,1,by simp⟩ : Submonoid.powers (f*g))
  change IsUnit (algebraMap R (Module.End R (Loc (f*g) M)) (f*g)) at h
  rw [map_mul] at h
  exact (((Commute.all f g).map (algebraMap R (Module.End R (Loc (f*g) M)))).isUnit_mul_iff.mp h).2

def overlapLeft (f g : R) : Loc f M →ₗ[R] Loc (f*g) M :=
  IsLocalizedModule.lift (Submonoid.powers f) (loc f) (loc (f*g)) (by
    rintro ⟨r,n,rfl⟩
    simpa using (overlap_units_left (M := M) f g).pow n)

def overlapRight (f g : R) : Loc g M →ₗ[R] Loc (f*g) M :=
  IsLocalizedModule.lift (Submonoid.powers g) (loc g) (loc (f*g)) (by
    rintro ⟨r,n,rfl⟩
    simpa using (overlap_units_right (M := M) f g).pow n)

@[simp] theorem overlapLeft_loc (f g : R) (m : M) : overlapLeft f g (loc f m)=loc (f*g) m :=
  IsLocalizedModule.lift_apply ..
@[simp] theorem overlapRight_loc (f g : R) (m : M) : overlapRight f g (loc g m)=loc (f*g) m :=
  IsLocalizedModule.lift_apply ..

theorem cleared_denominator (f : R) (x : Loc f M) :
    ∃ b : M,∃ n : ℕ,f^n • x=loc f b := by
  obtain ⟨⟨b,⟨s,n,rfl⟩⟩,hx⟩ := IsLocalizedModule.surj (Submonoid.powers f) (loc f) x
  exact ⟨b,n,hx⟩

/-- Kernel of restriction to D(fg), after f has already been inverted,
consists precisely (in this needed direction) of g-power torsion. -/
theorem overlap_kernel (f g : R) (x : Loc f M) (hx : overlapLeft f g x=0) :
    ∃ k : ℕ,g^k • x=0 := by
  obtain ⟨b,n,hb⟩ := cleared_denominator f x
  have hzero : loc (f*g) b=0 := by
    have h := congrArg (overlapLeft f g) hb
    simpa only [map_smul,hx,smul_zero,overlapLeft_loc] using h.symm
  obtain ⟨⟨s,k,rfl⟩,hk⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers (f*g)) (loc (f*g))).1 hzero
  change (f*g)^k • b=0 at hk
  refine ⟨k,?_⟩
  apply IsLocalizedModule.smul_injective (loc f) (⟨f^(k+n),k+n,rfl⟩ : Submonoid.powers f)
  change f^(k+n) • (g^k • x)=f^(k+n) • (0 : Loc f M)
  rw [smul_zero]
  have h := congrArg (loc f) hk
  simp only [map_smul,map_zero,← hb] at h
  convert h using 1 <;> simp only [smul_smul] <;> congr 1 <;> ring

theorem cover_injective {ι : Type*} (f : ι → R) (hf : Ideal.span (range f)=⊤)
    (x y : M) (h : ∀ i,loc (f i) x=loc (f i) y) : x=y := by
  apply Module.eq_of_isLocalized_span (range f) hf
    (fun r : range f => Loc r.val M) (fun r => loc r.val) x y
  rintro ⟨r,⟨i,rfl⟩⟩
  exact h i

/-- Concrete finite-principal-cover descent. Neither M nor any source of a
later map is assumed finitely generated or finitely presented. -/
theorem element_gluing {m : ℕ} (f : Fin m → R) (hf : Ideal.span (range f)=⊤)
    (x : ∀ i,Loc (f i) M)
    (hc : ∀ i j,overlapLeft (f i) (f j) (x i)=overlapRight (f i) (f j) (x j)) :
    ∃! b : M,∀ i,loc (f i) b=x i := by
  classical
  choose b n hn using fun j => cleared_denominator (f j) (x j)
  have ht (i j : Fin m) : ∃ k : ℕ,(f j)^k • (loc (f i) (b j)-(f j)^(n j) • x i)=0 := by
    apply overlap_kernel (f i) (f j)
    rw [map_sub,map_smul,overlapLeft_loc,hc i j,← map_smul,hn j,overlapRight_loc,sub_self]
  choose k hk using ht
  let L : ℕ := Finset.univ.sup (fun j => n j+Finset.univ.sup (fun i => k i j))
  have hL (i j : Fin m) : k i j+n j≤L := by
    have h₁ : k i j≤Finset.univ.sup (fun i => k i j) := Finset.le_sup (f := fun i : Fin m => k i j) (Finset.mem_univ i)
    have h₂ : n j+Finset.univ.sup (fun i => k i j)≤L := Finset.le_sup (f := fun j : Fin m => n j+Finset.univ.sup (fun i => k i j)) (Finset.mem_univ j)
    omega
  have hnL (j : Fin m) : n j≤L := by
    have h := (Finset.le_sup (f := fun j : Fin m => n j+Finset.univ.sup (fun i => k i j)) (Finset.mem_univ j) : n j+Finset.univ.sup (fun i => k i j)≤L)
    omega
  let b' (j : Fin m) := (f j)^(L-n j) • b j
  have hb' (i j : Fin m) : loc (f i) (b' j)=(f j)^L • x i := by
    have h := congrArg (fun z : Loc (f i) M => (f j)^(L-n j-k i j) • z) (hk i j)
    have he₁ : L-n j-k i j+k i j=L-n j := by have := hL i j;omega
    have he₂ : L-n j+n j=L := Nat.sub_add_cancel (hnL j)
    simp only [smul_zero,smul_smul,← pow_add,he₁] at h
    rw [smul_sub,smul_smul,← pow_add,he₂,sub_eq_zero] at h
    simpa only [b',map_smul] using h
  have hpow : Ideal.span (range (fun i => (f i)^L))=⊤ := by
    simpa only [← Set.range_comp,Function.comp_def] using Ideal.span_pow_eq_top (range f) hf L
  have hone : (1 : R)∈Submodule.span R (range (fun i => (f i)^L)) := by
    change (1 : R)∈Ideal.span (range (fun i => (f i)^L))
    rw [hpow]
    trivial
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hone
  refine ⟨∑ j,c j • b' j,?_,?_⟩
  · intro i
    simp only [map_sum,map_smul,hb',smul_smul]
    rw [← Finset.sum_smul]
    have he : ∑ j,c j*(f j)^L=1 := by simpa only [smul_eq_mul] using hc
    rw [he,one_smul]
  · intro z hz
    apply cover_injective f hf z (∑ j,c j • b' j)
    intro i
    rw [hz i]
    symm
    simp only [map_sum,map_smul,hb',smul_smul]
    rw [← Finset.sum_smul]
    have he : ∑ j,c j*(f j)^L=1 := by simpa only [smul_eq_mul] using hc
    rw [he,one_smul]

end MathGauge.PrincipalGluing
