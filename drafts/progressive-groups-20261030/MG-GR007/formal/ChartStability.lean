import AffineTower
import EventualTower

noncomputable section
namespace MathGauge.GR007.ChartStability
universe u v w
variable {k : Type u} [Field k]
variable {W : ℕ → Type v} [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)]
variable {X : ℕ → Type w} (e : ∀ n, W n ≃ X n) (f : ∀ n, X (n+1) → X n)
variable (L : ∀ n, W (n+1) →ₗ[k] W n) (d : ∀ n, W n)
variable (hf : ∀ n u, f n (e (n+1) u)=e n (AffineTower.step L d n u))
include hf

theorem down_coordinates (n m : ℕ) (h : n ≤ m) (u : W m) :
    EventualTower.down f n m h (e m u)=e n (AffineTower.down L d n m h u) := by
  induction m,h using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [EventualTower.down_succ f n m hm,Function.comp_apply,hf,ih]
    rw [AffineTower.down_comp L d n m (m+1) hm (Nat.le_succ m),AffineTower.down_adjacent]

def stable (n : ℕ) : Set (X n) :=
  ⋂ (m : ℕ) (h : n ≤ m),Set.range (EventualTower.down f n m h)

theorem range_coordinates (n m : ℕ) (h : n ≤ m) :
    Set.range (EventualTower.down f n m h)=e n '' AffineTower.image L d n m h := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    obtain ⟨u,rfl⟩ := (e m).surjective y
    exact ⟨AffineTower.down L d n m h u,⟨u,rfl⟩,(down_coordinates e f L d hf n m h u).symm⟩
  · rintro ⟨y,⟨u,rfl⟩,rfl⟩
    exact ⟨e m u,down_coordinates e f L d hf n m h u⟩

theorem stable_coordinates (n : ℕ) :
    stable f n=e n '' AffineTower.stable L d n := by
  ext x
  simp only [stable,Set.mem_iInter,Set.mem_range,Set.mem_image]
  constructor
  · intro hx
    refine ⟨(e n).symm x,?_,(e n).apply_symm_apply x⟩
    rw [AffineTower.mem_stable]
    intro m hm
    obtain ⟨y,hy⟩ := hx m hm
    obtain ⟨u,rfl⟩ := (e m).surjective y
    refine ⟨u,?_⟩
    apply (e n).injective
    rw [← down_coordinates e f L d hf,hy,(e n).apply_symm_apply]
  · rintro ⟨u,hu,rfl⟩ m hm
    obtain ⟨v,hv⟩ := (AffineTower.mem_stable L d n u).mp hu m hm
    refine ⟨e m v,?_⟩
    rw [down_coordinates e f L d hf,hv]

theorem actual_images_stabilize [∀ n, FiniteDimensional k (W n)] (n : ℕ) :
    ∃ N, ∃ hN : n ≤ N, ∀ m, ∀ hm : N ≤ m,
      Set.range (EventualTower.down f n N hN)=Set.range (EventualTower.down f n m (hN.trans hm)) := by
  obtain ⟨N,hN,h⟩ := AffineTower.images_stabilize L d n
  refine ⟨N,hN,fun m hm => ?_⟩
  rw [range_coordinates e f L d hf,range_coordinates e f L d hf,h m hm]

theorem actual_stable_surjective [∀ n, FiniteDimensional k (W n)] (n : ℕ) :
    ∀ x∈stable f n, ∃ y∈stable f (n+1),f n y=x := by
  intro x hx
  rw [stable_coordinates e f L d hf] at hx
  obtain ⟨u,hu,rfl⟩ := hx
  obtain ⟨v,hv,hstep⟩ := AffineTower.step_stable_surjective L d n u hu
  refine ⟨e (n+1) v,?_,?_⟩
  · rw [stable_coordinates e f L d hf]
    exact ⟨v,hv,rfl⟩
  · rw [hf,hstep]

end MathGauge.GR007.ChartStability
