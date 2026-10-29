import TowerChoices

noncomputable section
namespace MathGauge.GR006
open MathGauge.AbelianTower
universe u
variable {A B C A' B' : ℕ → Type u}
variable [∀ n, AddCommGroup (A n)] [∀ n, AddCommGroup (B n)] [∀ n, AddCommGroup (C n)]
variable [∀ n, AddCommGroup (A' n)] [∀ n, AddCommGroup (B' n)]
variable (a : ∀ n, A (n+1) →+ A n) (b : ∀ n, B (n+1) →+ B n)
variable (a' : ∀ n, A' (n+1) →+ A' n) (b' : ∀ n, B' (n+1) →+ B' n)
variable (i : ∀ n, A n →+ B n) (i' : ∀ n, A' n →+ B' n)
variable (hb : ∀ n, (b n).comp (i (n+1))=(i n).comp (a n))
variable (hb' : ∀ n, (b' n).comp (i' (n+1))=(i' n).comp (a' n))
variable (f : ∀ n, A n →+ A' n) (g : ∀ n, B n →+ B' n)
variable (hf : ∀ n, (a' n).comp (f (n+1))=(f n).comp (a n))
variable (hg : ∀ n, (b' n).comp (g (n+1))=(g n).comp (b n))
variable (hgi : ∀ n, (g n).comp (i n)=(i' n).comp (f n))

include hgi in
/-- Every supplied commuting square of towers gives the actual commuting
square on compatible sequences, for arbitrary (not merely iso) maps. -/
theorem limit_square (z : limit a) :
    limitMap b b' g hg (limitMap a b i hb z)=
      limitMap a' b' i' hb' (limitMap a a' f hf z) := by
  apply Subtype.ext
  funext n
  exact congrArg (fun h : A n →+ B' n => h (z.val n)) (hgi n)

include hgi in
theorem kernel_action_natural (x : limit b) (z : limit a) :
    limitMap b b' g hg (x+limitMap a b i hb z)=
      limitMap b b' g hg x+limitMap a' b' i' hb' (limitMap a a' f hf z) := by
  rw [map_add,limit_square a b a' b' i i' hb hb' f g hf hg hgi]

variable (c : ∀ n, C (n+1) →+ C n) (p : ∀ n, B n →+ C n)
variable (hp : ∀ n, (c n).comp (p (n+1))=(p n).comp (b n))
variable (hex : ∀ n, (i n).range=(p n).ker)

include hex in
theorem kernel_translation_preserves_record (x : limit b) (z : limit a) :
    limitMap b c p hp (x+limitMap a b i hb z)=limitMap b c p hp x := by
  rw [map_add]
  have hz : limitMap b c p hp (limitMap a b i hb z)=0 := by
    apply Subtype.ext
    funext n
    exact pi_i i p hex n (z.val n)
  rw [hz,add_zero]

end MathGauge.GR006
