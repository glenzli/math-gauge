import Mathlib.Topology.Algebra.Module.LinearMap
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Tactic

noncomputable section
open Filter Topology
namespace MathGauge.CyclicPotential
variable {H : Type*} [AddCommGroup H] [Module ℝ H] [TopologicalSpace H]
  [IsTopologicalAddGroup H] [ContinuousSMul ℝ H]

/-- Finite path integral, with the last edge ending at the variable point. -/
def path_value (a : H × (H →L[ℝ] ℝ)) : List (H × (H →L[ℝ] ℝ)) → H → ℝ
  | [], x => a.2 (x-a.1)
  | b::l, x => a.2 (b.1-a.1) + path_value b l x

/-- Closing every finite path yields the standard cyclic-monotonicity inequalities. -/
def CyclicMonotone (Γ : Set (H × (H →L[ℝ] ℝ))) : Prop :=
  ∀ a ∈ Γ, ∀ l : List (H × (H →L[ℝ] ℝ)), (∀ b ∈ l, b ∈ Γ) → path_value a l a.1 ≤ 0

def ValidPath (Γ : Set (H × (H →L[ℝ] ℝ))) := {l : List (H × (H →L[ℝ] ℝ)) // ∀ a ∈ l, a ∈ Γ}

instance (Γ : Set (H × (H →L[ℝ] ℝ))) : Inhabited (ValidPath Γ) := ⟨⟨[],by simp⟩⟩

@[simp] theorem path_nil (a : H × (H →L[ℝ] ℝ)) (x : H) : path_value a [] x = a.2 (x-a.1) := rfl

theorem path_append (a b : H × (H →L[ℝ] ℝ)) (l : List (H × (H →L[ℝ] ℝ))) (x : H) :
    path_value a (l++[b]) x = path_value a l b.1 + b.2 (x-b.1) := by
  induction l generalizing a with
  | nil => rfl
  | cons c l ih => simp only [List.cons_append,path_value,ih]; ring

theorem path_affine (a : H × (H →L[ℝ] ℝ)) (l : List (H × (H →L[ℝ] ℝ))) (x y : H) (s t : ℝ)
    (hst : s+t=1) :
    path_value a l (s • x + t • y) = s*path_value a l x+t*path_value a l y := by
  induction l generalizing a with
  | nil =>
    simp only [path_value,map_sub,map_add,map_smul,smul_eq_mul]
    have hs : s=1-t := by linarith
    rw [hs]; ring
  | cons b l ih =>
    simp only [path_value,ih]
    have hs : s=1-t := by linarith
    rw [hs]; ring

theorem path_continuous (a : H × (H →L[ℝ] ℝ)) (l : List (H × (H →L[ℝ] ℝ))) : Continuous (path_value a l) := by
  induction l generalizing a with
  | nil => simp only [path_value]; fun_prop
  | cons b l ih => exact continuous_const.add (ih b)

/-- No optimizer, convex potential or subgradient certificate occurs in this definition. -/
def potential (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ)) (x : H) : EReal :=
  ⨆ p : ValidPath Γ, (path_value a p.val x : EReal)

theorem path_le_potential (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ)) (p : ValidPath Γ) (x : H) :
    (path_value a p.val x : EReal) ≤ potential Γ a x := by
  exact le_iSup (fun q : ValidPath Γ => (path_value a q.val x : EReal)) p

theorem potential_ne_bot (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ)) (x : H) : potential Γ a x ≠ ⊥ := by
  have h := path_le_potential Γ a (default : ValidPath Γ) x
  exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h

theorem potential_le_real_iff (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ)) (x : H) (r : ℝ) :
    potential Γ a x ≤ (r : EReal) ↔ ∀ p : ValidPath Γ, path_value a p.val x ≤ r := by
  simp [potential,iSup_le_iff]

theorem potential_base (Γ : Set (H × (H →L[ℝ] ℝ))) (hΓ : CyclicMonotone Γ) (a : H × (H →L[ℝ] ℝ)) (ha : a∈Γ) :
    potential Γ a a.1 = 0 := by
  apply le_antisymm
  · rw [← EReal.coe_zero, potential_le_real_iff]
    exact fun p => hΓ a ha p.val p.property
  · simpa [path_value] using path_le_potential Γ a (⟨[],by simp⟩ : ValidPath Γ) a.1

theorem potential_upper_on_graph (Γ : Set (H × (H →L[ℝ] ℝ))) (hΓ : CyclicMonotone Γ)
    (a b : H × (H →L[ℝ] ℝ)) (ha : a∈Γ) (hb : b∈Γ) :
    potential Γ a b.1 ≤ (b.2 (b.1-a.1) : EReal) := by
  rw [potential_le_real_iff]
  intro p
  have h := hΓ a ha (p.val++[b]) (by
    intro c hc
    rcases List.mem_append.mp hc with hc|hc
    · exact p.property c hc
    · have hcb : c=b := by simpa using hc
      exact hcb ▸ hb)
  rw [path_append] at h
  have he : b.2 (a.1-b.1) = -b.2 (b.1-a.1) := by
    simp only [map_sub]; ring
  rw [he] at h
  linarith

theorem potential_finite_on_graph (Γ : Set (H × (H →L[ℝ] ℝ))) (hΓ : CyclicMonotone Γ)
    (a b : H × (H →L[ℝ] ℝ)) (ha : a∈Γ) (hb : b∈Γ) :
    ∃ r : ℝ, potential Γ a b.1 = (r : EReal) := by
  have htop : potential Γ a b.1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (potential_upper_on_graph Γ hΓ a b ha hb)
  exact ⟨(potential Γ a b.1).toReal,
    (EReal.coe_toReal htop (potential_ne_bot Γ a b.1)).symm⟩

/-- A real-height epigraph; this is the conventional convexity convention for extended potentials. -/
def real_epigraph (f : H → EReal) : Set (H×ℝ) := {z | f z.1 ≤ (z.2 : EReal)}

theorem potential_epigraph_convex (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ)) :
    Convex ℝ (real_epigraph (potential Γ a)) := by
  intro x hx y hy s t hs ht hst
  change potential Γ a (s • x.1+t • y.1) ≤ ((s*x.2+t*y.2 : ℝ) : EReal)
  rw [potential_le_real_iff]
  intro p
  rw [path_affine a p.val x.1 y.1 s t hst]
  exact add_le_add (mul_le_mul_of_nonneg_left
    ((potential_le_real_iff Γ a x.1 x.2).1 hx p) hs)
    (mul_le_mul_of_nonneg_left ((potential_le_real_iff Γ a y.1 y.2).1 hy p) ht)

theorem potential_epigraph_closed (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ)) :
    IsClosed (real_epigraph (potential Γ a)) := by
  have he : real_epigraph (potential Γ a) =
      ⋂ p : ValidPath Γ, {z : H×ℝ | path_value a p.val z.1 ≤ z.2} := by
    ext z
    simp [real_epigraph,potential_le_real_iff]
  rw [he]
  exact isClosed_iInter (fun p => isClosed_le ((path_continuous a p.val).comp continuous_fst)
    continuous_snd)

theorem potential_lsc (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ)) : LowerSemicontinuous (potential Γ a) :=
  lowerSemicontinuous_iSup (fun p : ValidPath Γ =>
    (continuous_coe_real_ereal.comp (path_continuous a p.val)).lowerSemicontinuous)

/-- Standard subgradient: the value at the base is finite and the affine support lies below f. -/
def Subgradient (f : H → EReal) (x : H) (y : H →L[ℝ] ℝ) : Prop :=
  ∃ r : ℝ, f x = (r : EReal) ∧ ∀ z : H, ((r+y (z-x) : ℝ) : EReal) ≤ f z

theorem potential_subgradient (Γ : Set (H × (H →L[ℝ] ℝ))) (hΓ : CyclicMonotone Γ)
    (a b : H × (H →L[ℝ] ℝ)) (ha : a∈Γ) (hb : b∈Γ) : Subgradient (potential Γ a) b.1 b.2 := by
  obtain ⟨r,hr⟩ := potential_finite_on_graph Γ hΓ a b ha hb
  refine ⟨r,hr,?_⟩
  intro z
  let c := b.2 (z-b.1)
  have h : potential Γ a b.1 ≤ potential Γ a z - (c : EReal) := by
    apply iSup_le
    intro p
    apply (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot c))
      (Or.inl (EReal.coe_ne_top c))).2
    rw [← EReal.coe_add]
    let p' : ValidPath Γ := ⟨p.val++[b], by
      intro d hd
      rcases List.mem_append.mp hd with hd|hd
      · exact p.property d hd
      · have hdb : d=b := by simpa using hd
        exact hdb ▸ hb⟩
    simpa [p',path_append,c] using path_le_potential Γ a p' z
  rw [hr] at h
  simpa [EReal.coe_add,c] using
    (EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))).1 h

/-- Every supporting potential dominates every finite path; this is proved by induction. -/
theorem path_le_supporting (Γ : Set (H × (H →L[ℝ] ℝ))) (g : H→EReal)
    (hg : ∀ b∈Γ, Subgradient g b.1 b.2)
    (a : H × (H →L[ℝ] ℝ)) (ha : a∈Γ) (l : List (H × (H →L[ℝ] ℝ))) (hl : ∀ b∈l, b∈Γ)
    (r : ℝ) (hr : g a.1=(r:EReal)) (z : H) :
    ((r+path_value a l z : ℝ) : EReal) ≤ g z := by
  induction l generalizing a r with
  | nil =>
    obtain ⟨q,hq,hineq⟩ := hg a ha
    have hqr : q=r := EReal.coe_injective (hq.symm.trans hr)
    simpa [path_value,hqr] using hineq z
  | cons b l ih =>
    have hb : b∈Γ := hl b (by simp)
    obtain ⟨q,hq,hineq⟩ := hg b hb
    obtain ⟨r',hr',haineq⟩ := hg a ha
    have hr'r : r'=r := EReal.coe_injective (hr'.symm.trans hr)
    have hab : r+a.2 (b.1-a.1) ≤ q := by
      have h := haineq b.1
      rw [hq,hr'r] at h
      exact EReal.coe_le_coe_iff.mp h
    have hi := ih b hb (fun d hd => hl d (by simp [hd])) q hq
    apply le_trans (EReal.coe_le_coe (show r+path_value a (b::l) z ≤ q+path_value b l z by
      simp only [path_value]; linarith)) hi

theorem potential_minimal (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ)) (ha : a∈Γ)
    (g : H→EReal) (hg0 : g a.1=0) (hg : ∀ b∈Γ, Subgradient g b.1 b.2) :
    ∀ z, potential Γ a z ≤ g z := by
  intro z
  apply iSup_le
  intro p
  simpa using path_le_supporting Γ g hg a ha p.val p.property 0 (by simpa using hg0) z

/-- Full original target on the actual supremum potential. -/
theorem main (Γ : Set (H × (H →L[ℝ] ℝ))) (hΓ : CyclicMonotone Γ) (a : H × (H →L[ℝ] ℝ)) (ha : a∈Γ) :
    (∀ x, potential Γ a x ≠ ⊥) ∧ potential Γ a a.1=0 ∧
    LowerSemicontinuous (potential Γ a) ∧ Convex ℝ (real_epigraph (potential Γ a)) ∧
    (∀ b∈Γ, Subgradient (potential Γ a) b.1 b.2) ∧
    (∀ g : H→EReal, g a.1=0 → (∀ b∈Γ, Subgradient g b.1 b.2) →
      ∀ z, potential Γ a z ≤ g z) :=
  ⟨potential_ne_bot Γ a,potential_base Γ hΓ a ha,potential_lsc Γ a,
    potential_epigraph_convex Γ a,(fun b hb => potential_subgradient Γ hΓ a b ha hb),
    (fun g hg0 hg => potential_minimal Γ a ha g hg0 hg)⟩

/-- Uniqueness is pointwise equality, including infinite values. -/
theorem least_unique {f g : H→EReal} (hfg : ∀x, f x ≤ g x) (hgf : ∀x, g x ≤ f x) : f=g := by
  funext x
  exact le_antisymm (hfg x) (hgf x)

def singleton_graph : Set (ℝ × (ℝ →L[ℝ] ℝ)) := {(0,0)}

theorem singleton_path_zero (l : List (ℝ × (ℝ →L[ℝ] ℝ)))
    (hl : ∀b∈l, b∈singleton_graph) (x : ℝ) : path_value (0,0) l x=0 := by
  induction l with
  | nil => simp [path_value]
  | cons b l ih =>
    have hb : b=(0,0) := hl b (by simp)
    subst b
    simp only [path_value, ContinuousLinearMap.zero_apply, zero_add]
    exact ih (fun c hc => hl c (by simp [hc]))

theorem singleton_cyclic : CyclicMonotone singleton_graph := by
  intro a ha l hl
  have ha' : a=(0,0) := ha
  subst a
  exact le_of_eq (singleton_path_zero l hl _)

theorem singleton_potential_zero : potential singleton_graph (0,0) = fun _ => 0 := by
  funext x
  change (⨆ p : ValidPath singleton_graph, (path_value (0,0) p.val x : EReal))=0
  have he : (fun p : ValidPath singleton_graph => (path_value (0,0) p.val x : EReal)) =
      fun _ => (0 : EReal) := by
    funext p
    rw [singleton_path_zero p.val p.property x, EReal.coe_zero]
  rw [he]
  simp

theorem singleton_strict_extension :
    Subgradient (potential singleton_graph (0,0)) 1 0 ∧ (1,0)∉singleton_graph := by
  constructor
  · rw [singleton_potential_zero]
    refine ⟨0,rfl,?_⟩
    intro z
    simp
  · norm_num [singleton_graph]

end MathGauge.CyclicPotential
