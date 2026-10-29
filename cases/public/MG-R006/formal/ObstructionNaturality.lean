import Obstruction

noncomputable section
namespace MathGauge.AbelianTower
universe u
variable {A B C A' B' C' : ℕ → Type u}
variable [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] [∀ n, AddCommGroup (C n)]
variable [∀ n, AddCommGroup (A' n)] [∀ n, AddCommGroup (B' n)] [∀ n, AddCommGroup (C' n)]
variable (a : ∀ n, A (n+1) →+ A n) (a' : ∀ n, A' (n+1) →+ A' n)
variable (f : ∀ n, A n →+ A' n)
variable (hf : ∀ n, (a' n).comp (f (n+1))=(f n).comp (a n))

/-- The actual product map descends to the cokernel of the difference map. -/
def obstructionMap : ObstructionGroup a →+ ObstructionGroup a' :=
  QuotientAddGroup.map (delta a).range (delta a').range (productMap f) (by
    rintro d ⟨x,rfl⟩
    exact ⟨productMap f x,delta_natural a a' f hf x⟩)

@[simp] theorem obstructionMap_mk (d : ∀ n, A n) :
    obstructionMap a a' f hf ((QuotientAddGroup.mk' (delta a).range) d)=
      (QuotientAddGroup.mk' (delta a').range) (productMap f d) :=
  QuotientAddGroup.map_mk' _ _ _ _ _

variable (b : ∀ n, B (n+1) →+ B n) (c : ∀ n, C (n+1) →+ C n)
variable (i : ∀ n, A n →+ B n) (p : ∀ n, B n →+ C n)
variable (b' : ∀ n, B' (n+1) →+ B' n) (c' : ∀ n, C' (n+1) →+ C' n)
variable (i' : ∀ n, A' n →+ B' n) (p' : ∀ n, B' n →+ C' n)
variable (hex : ∀ n, (i n).range=(p n).ker) (hi : ∀ n, Function.Injective (i n))
variable (hb : ∀ n, (b n).comp (i (n+1))=(i n).comp (a n))
variable (hp : ∀ n, (c n).comp (p (n+1))=(p n).comp (b n))
variable (hs : ∀ n, Function.Surjective (p n))
variable (hex' : ∀ n, (i' n).range=(p' n).ker) (hi' : ∀ n, Function.Injective (i' n))
variable (hb' : ∀ n, (b' n).comp (i' (n+1))=(i' n).comp (a' n))
variable (hp' : ∀ n, (c' n).comp (p' (n+1))=(p' n).comp (b' n))
variable (hs' : ∀ n, Function.Surjective (p' n))
variable (g : ∀ n, B n →+ B' n) (h : ∀ n, C n →+ C' n)
variable (hg : ∀ n, (b' n).comp (g (n+1))=(g n).comp (b n))
variable (hh : ∀ n, (c' n).comp (h (n+1))=(h n).comp (c n))
variable (hgi : ∀ n, (g n).comp (i n)=(i' n).comp (f n))
variable (hph : ∀ n, (p' n).comp (g n)=(h n).comp (p n))

include hg hgi hph in
/-- The connecting obstruction commutes with every morphism of the given exact towers. -/
theorem obstruction_natural (r : limit c) :
    obstructionMap a a' f hf (obstruction a b i c p hex hi hb hp hs r)=
    obstruction a' b' i' c' p' hex' hi' hb' hp' hs' (limitMap c c' h hh r) := by
  let x := chosenLift c p hs r
  let d := chosenDefect a b i c p hex hi hb hp hs r
  have hl : ∀ n, p' n (productMap g x n)=(limitMap c c' h hh r).val n := by
    intro n
    change p' n (g n (x n))=h n (r.val n)
    have hn := congrArg (fun m : B n →+ C' n => m (x n)) (hph n)
    change p' n (g n (x n))=h n (p n (x n)) at hn
    rw [hn,chosenLift_spec]
  have hd : productMap i' (productMap f d)=delta b' (productMap g x) := by
    rw [delta_natural b b' g hg]
    funext n
    change i' n (f n (d n))=g n (delta b x n)
    rw [← chosenDefect_spec a b i c p hex hi hb hp hs r n]
    exact (congrArg (fun m : A n →+ B' n => m (d n)) (hgi n)).symm
  rw [obstruction_of_lift a' b' i' c' p' hex' hi' hb' hp' hs' _ _ hl _ hd]
  exact obstructionMap_mk a a' f hf d

include hex hi hb hp hs in
/-- Under the stated B-surjectivity, the obstruction group is trivial exactly when every compatible record lifts. -/
theorem obstruction_trivial_iff (hbs : ∀ n, Function.Surjective (b n)) :
    (∀ z : ObstructionGroup a, z=0) ↔ Function.Surjective (limitMap b c p hp) := by
  constructor
  · intro hz r
    exact (obstruction_zero_iff a b i c p hex hi hb hp hs r).mp (hz _)
  · intro ht z
    obtain ⟨r,hr⟩ := obstruction_surjective a b i c p hex hi hb hp hs hbs z
    rw [← hr]
    exact (obstruction_zero_iff a b i c p hex hi hb hp hs r).mpr (ht r)

end MathGauge.AbelianTower
