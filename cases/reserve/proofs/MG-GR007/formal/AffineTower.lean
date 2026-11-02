import LinearTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace MathGauge.GR007.AffineTower
open MathGauge.LinearTower
universe u v
variable {k : Type u} [Field k]
variable {W : ℕ → Type v} [∀ n, AddCommGroup (W n)] [∀ n, Module k (W n)]
variable (L : ∀ n, W (n+1) →ₗ[k] W n) (d : ∀ n, W n)

def step (n : ℕ) (x : W (n+1)) : W n := L n x+d n

/-- Homogenization adds one scalar coordinate to the actual direction
space, never to the possibly infinite-dimensional ambient B_n. -/
def homogeneous (n : ℕ) : (W (n+1)×k) →ₗ[k] (W n×k) where
  toFun x := (L n x.1+x.2 • d n,x.2)
  map_add' x y := by ext <;> simp [add_smul] <;> abel
  map_smul' a x := by ext <;> simp [smul_add,smul_smul]

theorem homogeneous_record (n : ℕ) :
    (LinearMap.snd k (W n) k).comp (homogeneous L d n)=LinearMap.snd k (W (n+1)) k := rfl

theorem down_record (n m : ℕ) (h : n ≤ m) (x : W m×k) :
    (MathGauge.LinearTower.down (V := fun n => W n × k) (homogeneous L d) n m h x).2=x.2 := by
  exact congrArg (fun f : (W m×k) →ₗ[k] k => f x)
    (MathGauge.LinearTower.down_record (V := fun n => W n × k) (homogeneous L d)
      (fun n => LinearMap.snd k (W n) k) (homogeneous_record L d) n m h)

def down (n m : ℕ) (h : n ≤ m) (x : W m) : W n :=
  (MathGauge.LinearTower.down (V := fun n => W n × k) (homogeneous L d) n m h (x,1)).1

theorem down_pair (n m : ℕ) (h : n ≤ m) (x : W m) :
    MathGauge.LinearTower.down (V := fun n => W n × k) (homogeneous L d) n m h (x,1)=(down L d n m h x,1) := by
  exact Prod.ext rfl (down_record L d n m h (x,1))

@[simp] theorem down_self (n : ℕ) : down L d n n le_rfl=id := by
  funext x; simp [down]

@[simp] theorem down_adjacent (n : ℕ) (x : W (n+1)) :
    down L d n (n+1) (Nat.le_succ n) x=step L d n x := by
  simp [down,MathGauge.LinearTower.down_adjacent,homogeneous,step]

theorem down_comp (n m l : ℕ) (h : n ≤ m) (h' : m ≤ l) (x : W l) :
    down L d n l (h.trans h') x=down L d n m h (down L d m l h' x) := by
  unfold down
  rw [MathGauge.LinearTower.down_comp (V := fun n => W n × k) (homogeneous L d) n m l h h',LinearMap.comp_apply,
    down_pair L d m l h' x]

def image (n m : ℕ) (h : n ≤ m) : Set (W n) := Set.range (down L d n m h)

theorem images_stabilize [∀ n, FiniteDimensional k (W n)] (n : ℕ) :
    ∃ N, ∃ hN : n ≤ N, ∀ m, ∀ hm : N ≤ m,
      image L d n N hN=image L d n m (hN.trans hm) := by
  obtain ⟨N,hN,hstab⟩ := MathGauge.LinearTower.ranges_stabilize (V := fun n => W n × k) (homogeneous L d) n
  refine ⟨N,hN,fun m hm => ?_⟩
  ext x
  constructor
  · rintro ⟨y,hy⟩
    have hh : (x,1) ∈ LinearMap.range (MathGauge.LinearTower.down (V := fun n => W n × k) (homogeneous L d) n N hN) :=
      ⟨(y,1),by rw [down_pair,hy]⟩
    rw [hstab m hm] at hh
    obtain ⟨z,hz⟩ := hh
    have hs : z.2=1 := (down_record L d n m _ z).symm.trans (congrArg Prod.snd hz)
    refine ⟨z.1,?_⟩
    have he : z=(z.1,1) := Prod.ext rfl hs
    rw [he,down_pair] at hz
    exact congrArg Prod.fst hz
  · rintro ⟨y,hy⟩
    refine ⟨down L d N m hm y,?_⟩
    rw [← down_comp]
    exact hy

def stable (n : ℕ) : Set (W n) := ⋂ (m : ℕ) (h : n ≤ m), image L d n m h

theorem mem_stable (n : ℕ) (x : W n) :
    x ∈ stable L d n ↔ ∀ m, ∀ h : n ≤ m, ∃ y, down L d n m h y=x := by
  simp [stable,image]

theorem stable_eq_image [∀ n, FiniteDimensional k (W n)] (n : ℕ) :
    ∃ N, ∃ hN : n ≤ N, ∀ m, ∀ hm : N ≤ m,
      stable L d n=image L d n m (hN.trans hm) := by
  obtain ⟨N,hN,hstab⟩ := images_stabilize L d n
  refine ⟨N,hN,fun m hm => Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    exact (mem_stable L d n x).mp hx m _
  · intro x hx
    rw [mem_stable]
    intro l hl
    let r := max m l
    have hNr : N ≤ r := hm.trans (le_max_left _ _)
    rw [(hstab m hm).symm,hstab r hNr] at hx
    obtain ⟨y,hy⟩ := hx
    exact ⟨down L d l r (le_max_right _ _) y,by rw [← down_comp]; exact hy⟩

theorem stable_nonempty [∀ n, FiniteDimensional k (W n)] (n : ℕ) :
    (stable L d n).Nonempty := by
  obtain ⟨N,hN,h⟩ := stable_eq_image L d n
  rw [h N le_rfl]
  exact ⟨_,⟨0,rfl⟩⟩

theorem step_stable {n : ℕ} {y : W (n+1)} (hy : y ∈ stable L d (n+1)) :
    step L d n y ∈ stable L d n := by
  rw [mem_stable] at hy ⊢
  intro m hm
  by_cases hmn : m=n
  · subst m
    exact ⟨step L d n y,by simp⟩
  · obtain ⟨z,hz⟩ := hy m (by omega)
    refine ⟨z,?_⟩
    rw [down_comp L d n (n+1) m (Nat.le_succ _) (by omega),down_adjacent,hz]

theorem step_stable_surjective [∀ n, FiniteDimensional k (W n)] (n : ℕ) :
    ∀ x ∈ stable L d n, ∃ y ∈ stable L d (n+1), step L d n y=x := by
  intro x hx
  obtain ⟨N,hN,hstab⟩ := stable_eq_image L d (n+1)
  obtain ⟨z,hz⟩ := (mem_stable L d n x).mp hx N (by omega)
  refine ⟨down L d (n+1) N hN z,?_,?_⟩
  · rw [hstab N le_rfl]
    exact ⟨z,rfl⟩
  · rw [← down_adjacent L d n,← down_comp]
    exact hz

theorem coherent [∀ n, FiniteDimensional k (W n)] :
    ∃ x : ∀ n, W n, ∀ n, step L d n (x (n+1))=x n := by
  obtain ⟨x,hq,hc⟩ := MathGauge.LinearTower.coherent_fiber (V := fun n => W n × k) (homogeneous L d)
    (fun n => LinearMap.snd k (W n) k) (homogeneous_record L d) (1 : k)
    (fun n => ⟨(0,1),rfl⟩)
  refine ⟨fun n => (x n).1,fun n => ?_⟩
  have hh := congrArg Prod.fst (hc n)
  change L n (x (n+1)).1+(x (n+1)).2 • d n=(x n).1 at hh
  change step L d n (x (n+1)).1=(x n).1
  have hq1 : (x (n+1)).2=1 := hq (n+1)
  simpa [step,hq1] using hh

end MathGauge.GR007.AffineTower
