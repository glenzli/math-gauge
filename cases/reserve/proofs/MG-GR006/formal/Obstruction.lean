import AbelianTower

noncomputable section
namespace MathGauge.AbelianTower
universe u
variable {A B C : ℕ → Type u}
variable [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] [∀ n, AddCommGroup (C n)]
variable (a : ∀ n, A (n+1) →+ A n) (b : ∀ n, B (n+1) →+ B n)
variable (i : ∀ n, A n →+ B n) (c : ∀ n, C (n+1) →+ C n) (p : ∀ n, B n →+ C n)
variable (hex : ∀ n, (i n).range = (p n).ker) (hi : ∀ n, Function.Injective (i n))
variable (hb : ∀ n, (b n).comp (i (n+1)) = (i n).comp (a n))
variable (hp : ∀ n, (c n).comp (p (n+1)) = (p n).comp (b n))
variable (hs : ∀ n, Function.Surjective (p n))

abbrev ObstructionGroup := (∀ n, A n) ⧸ (delta a).range

def chosenLift (r : limit c) (n : ℕ) : B n := (hs n (r.val n)).choose

theorem chosenLift_spec (r : limit c) (n : ℕ) : p n (chosenLift c p hs r n)=r.val n :=
  (hs n (r.val n)).choose_spec

def chosenDefect (r : limit c) : ∀ n, A n :=
  (defect_exists a b i c p hex hi hb hp r (chosenLift c p hs r) (chosenLift_spec c p hs r)).choose

theorem chosenDefect_spec (r : limit c) (n : ℕ) :
    i n (chosenDefect a b i c p hex hi hb hp hs r n)=delta b (chosenLift c p hs r) n :=
  (defect_exists a b i c p hex hi hb hp r (chosenLift c p hs r) (chosenLift_spec c p hs r)).choose_spec n

def obstruction (r : limit c) : ObstructionGroup a :=
  (QuotientAddGroup.mk' (delta a).range) (chosenDefect a b i c p hex hi hb hp hs r)

include hex hi hb hp
/-- The cokernel class is independent of every local choice. -/
theorem defect_class_independent (r : limit c)
    (x y : ∀ n, B n) (hx : ∀ n, p n (x n)=r.val n) (hy : ∀ n, p n (y n)=r.val n)
    (d e : ∀ n, A n) (hd : productMap i d=delta b x) (he : productMap i e=delta b y) :
    (QuotientAddGroup.mk' (delta a).range) d=(QuotientAddGroup.mk' (delta a).range) e := by
  have hk : ∀ n, p n (x n-y n)=0 := by intro n; rw [map_sub,hx n,hy n,sub_self]
  choose z hz using fun n => row_kernel i p hex n (hk n)
  have hz' : productMap i z=x-y := funext hz
  have hde : delta a z=d-e := by
    funext n
    apply hi n
    have h : productMap i (delta a z)=productMap i (d-e) := by
      rw [← delta_natural a b i hb,hz',map_sub,map_sub,hd,he]
    exact congrArg (fun t => t n) h
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  exact ⟨z,hde⟩

theorem obstruction_of_lift (r : limit c) (x : ∀ n, B n)
    (hx : ∀ n, p n (x n)=r.val n) (d : ∀ n, A n) (hd : productMap i d=delta b x) :
    obstruction a b i c p hex hi hb hp hs r=(QuotientAddGroup.mk' (delta a).range) d := by
  exact defect_class_independent a b i c p hex hi hb hp r
    (chosenLift c p hs r) x (chosenLift_spec c p hs r) hx
    (chosenDefect a b i c p hex hi hb hp hs r) d
    (funext (chosenDefect_spec a b i c p hex hi hb hp hs r)) hd

/-- Vanishing is equivalent to an actual compatible lift in the original groups. -/
theorem obstruction_zero_iff (r : limit c) :
    obstruction a b i c p hex hi hb hp hs r=0 ↔
    ∃ y : limit b, limitMap b c p hp y=r := by
  change (QuotientAddGroup.mk' (delta a).range) _=0 ↔ _
  change (QuotientAddGroup.mk _) = (0 : ObstructionGroup a) ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  exact (lift_iff_coboundary a b i c p hex hi hb hp r
    (chosenLift c p hs r) (chosenLift_spec c p hs r)
    (chosenDefect a b i c p hex hi hb hp hs r)
    (chosenDefect_spec a b i c p hex hi hb hp hs r)).symm

/-- The obstruction is an additive homomorphism, derived by using sums of actual lifts. -/
def obstructionHom : limit c →+ ObstructionGroup a where
  toFun := obstruction a b i c p hex hi hb hp hs
  map_zero' := by
    rw [obstruction_zero_iff]
    exact ⟨0,map_zero _⟩
  map_add' r s := by
    let x := chosenLift c p hs r
    let y := chosenLift c p hs s
    let d := chosenDefect a b i c p hex hi hb hp hs r
    let e := chosenDefect a b i c p hex hi hb hp hs s
    have hxy : ∀ n, p n ((x+y) n)=(r+s).val n := by
      intro n
      change p n (x n+y n)=r.val n+s.val n
      rw [map_add,chosenLift_spec,chosenLift_spec]
    have hde : productMap i (d+e)=delta b (x+y) := by
      rw [map_add,map_add]
      congr 1
      · exact funext (chosenDefect_spec a b i c p hex hi hb hp hs r)
      · exact funext (chosenDefect_spec a b i c p hex hi hb hp hs s)
    rw [obstruction_of_lift a b i c p hex hi hb hp hs (r+s) (x+y) hxy (d+e) hde]
    exact map_add _ d e

/-- Surjectivity of the B transitions makes the terminal obstruction map surjective. -/
theorem obstruction_surjective (hbs : ∀ n, Function.Surjective (b n)) :
    Function.Surjective (obstructionHom a b i c p hex hi hb hp hs) := by
  intro z
  obtain ⟨d,rfl⟩ := QuotientAddGroup.mk'_surjective (delta a).range z
  obtain ⟨x,hx⟩ := delta_surjective b hbs (productMap i d)
  have hr : productMap p x ∈ limit c := by
    change delta c (productMap p x)=0
    rw [delta_natural b c p hp,hx]
    funext n
    exact pi_i i p hex n (d n)
  let r : limit c := ⟨productMap p x,hr⟩
  refine ⟨r, ?_⟩
  exact obstruction_of_lift a b i c p hex hi hb hp hs r x (fun n => rfl) d hx.symm

include hs in
/-- Surjectivity in the kernel tower is a sufficient extra hypothesis, not inferred from B or C. -/
theorem surjective_limit_of_kernel_surjective (has : ∀ n, Function.Surjective (a n)) :
    Function.Surjective (limitMap b c p hp) := by
  intro r
  apply (obstruction_zero_iff a b i c p hex hi hb hp hs r).mp
  change (QuotientAddGroup.mk _) = (0 : ObstructionGroup a)
  rw [QuotientAddGroup.eq_zero_iff]
  exact delta_surjective a has _

/-- Every nonempty fiber is a torsor under the actual kernel inverse limit. -/
theorem lift_freedom (x y : limit b) (hxy : limitMap b c p hp y=limitMap b c p hp x) :
    ∃! z : limit a, y=x+limitMap a b i hb z := by
  have hh : limitMap b c p hp (y-x)=0 := by rw [map_sub,hxy,sub_self]
  obtain ⟨z,hz⟩ := limit_kernel a b i c p hex hi hb hp (y-x) hh
  refine ⟨z, ?_, ?_⟩
  · change y=x+limitMap a b i hb z
    rw [hz]; abel
  · intro z' hz'
    apply limitMap_injective a b i hb hi
    rw [hz]
    have := congrArg (fun t => t-x) hz'
    simpa [add_sub_cancel_left] using this.symm

end MathGauge.AbelianTower
