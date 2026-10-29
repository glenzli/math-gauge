import FinitePrefixes

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MathGauge.GR006
open MathGauge.AbelianTower CategoryTheory
universe u
variable {A B C : ℕ → Type u}
variable [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] [∀ n, AddCommGroup (C n)]
variable (b : ∀ n, B (n+1) →+ B n) (c : ∀ n, C (n+1) →+ C n)
variable (i : ∀ n, A n →+ B n) (p : ∀ n, B n →+ C n)
variable (hp : ∀ n, (c n).comp (p (n+1))=(p n).comp (b n))
variable (hex : ∀ n, (i n).range=(p n).ker) (hi : ∀ n, Function.Injective (i n))
variable (hs : ∀ n, Function.Surjective (p n))

/-- Each nonempty row fiber is in bijection with the actual kernel group. -/
def rowFiberEquiv (n : ℕ) (r : C n) (x : B n) (hx : p n x=r) :
    A n ≃ {y : B n // p n y=r} := by
  let f : A n → {y : B n // p n y=r} := fun a => ⟨x+i n a,by
    rw [map_add,hx,pi_i i p hex,add_zero]⟩
  apply Equiv.ofBijective f
  constructor
  · intro a a' h
    apply hi n
    exact add_left_cancel (congrArg Subtype.val h)
  · intro y
    obtain ⟨a,ha⟩ := row_kernel i p hex n (x := y.val-x) (by
      rw [map_sub,y.property,hx,sub_self])
    refine ⟨a,Subtype.ext ?_⟩
    change x+i n a=y.val
    rw [ha]
    abel

include hex hi hs in
/-- S5: finite kernels give actual finite lifting fibers. The resulting
inverse system need not have surjective arrows. -/
theorem finite_kernel_lift [∀ n, Finite (A n)] (r : limit c) :
    ∃ x : limit b, limitMap b c p hp x=r := by
  let X (n : ℕ) := {x : B n // p n x=r.val n}
  have hne : ∀ n, Nonempty (X n) := fun n => ⟨⟨(hs n (r.val n)).choose,(hs n (r.val n)).choose_spec⟩⟩
  letI : ∀ n, Nonempty (X n) := hne
  letI : ∀ n, Finite (X n) := fun n => Finite.of_equiv (A n)
    (rowFiberEquiv i p hex hi n (r.val n) (Classical.choice (hne n)).val
      (Classical.choice (hne n)).property)
  let f (n : ℕ) : X (n+1) → X n := fun x => ⟨b n x.val,by
    have hh := congrArg (fun t : B (n+1) →+ C n => t x.val) (hp n)
    change p n (b n x.val)=r.val n
    rw [← show c n (p (n+1) x.val)=p n (b n x.val) from hh,x.property]
    exact (mem_limit c r.val).mp r.property n⟩
  let F : ℕᵒᵖ ⥤ Type u := Functor.ofOpSequence f
  letI : ∀ n : ℕᵒᵖ, Finite (F.obj n) := fun n => inferInstanceAs (Finite (X n.unop))
  letI : ∀ n : ℕᵒᵖ, Nonempty (F.obj n) := fun n => inferInstanceAs (Nonempty (X n.unop))
  obtain ⟨z,hz⟩ := nonempty_sections_of_finite_inverse_system F
  let x : ∀ n, B n := fun n => (z ⟨n⟩).val
  have hx : x ∈ limit b := by
    rw [mem_limit]
    intro n
    have hh := hz ((homOfLE (Nat.le_succ n)).op)
    have he : f n (z ⟨n+1⟩)=z ⟨n⟩ := by
      simpa [F] using hh
    exact congrArg Subtype.val he
  refine ⟨⟨x,hx⟩,Subtype.ext ?_⟩
  funext n
  exact (z ⟨n⟩).property

end MathGauge.GR006
