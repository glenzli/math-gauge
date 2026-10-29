import Core

noncomputable section
open scoped BigOperators ENNReal NNReal
namespace MathGauge.RecursiveClosure
variable {Y V E I : Type} [Fintype I] {g : Gauge Y I}

/-- Original subset-and-partition data. No fixed point or convergence assertion is stored here. -/
structure PartitionData (Y V E I : Type) [Fintype I] (g : Gauge Y I) where
  U : V → Set Y
  nonempty : ∀ v, (U v).Nonempty
  src : E → V
  dst : E → V
  S : V → Set Y
  D : E → Set Y
  stop_subset : ∀ v, S v ⊆ U v
  call_subset : ∀ e, D e ⊆ U (src e)
  cover : ∀ v x, x ∈ U v → x ∈ S v ∨ ∃ e, src e=v ∧ x ∈ D e
  stop_disjoint : ∀ v e, src e=v → Disjoint (S v) (D e)
  call_disjoint : ∀ e f, src e=src f → e ≠ f → Disjoint (D e) (D f)
  terminal : ∀ v, S v → Y
  transfer : ∀ e, D e → U (dst e)
  ret : E → Y → Y
  L : E → I → I → ℝ≥0
  lip : ∀ e i x y, g.d i (ret e x) (ret e y) ≤ ∑ j, (L e i j : ℝ≥0∞)*g.d j x y

namespace PartitionData
variable (p : PartitionData Y V E I g)

def chosenEdge (v : V) (x : p.U v) (hx : x.val ∉ p.S v) : E :=
  ((p.cover v x.val x.property).resolve_left hx).choose

theorem chosenEdge_spec (v : V) (x : p.U v) (hx : x.val ∉ p.S v) :
    p.src (p.chosenEdge v x hx)=v ∧ x.val ∈ p.D (p.chosenEdge v x hx) :=
  ((p.cover v x.val x.property).resolve_left hx).choose_spec

def step (v : V) (x : p.U v) : Y ⊕ ((e : E) × p.U (p.dst e)) := by
  classical
  exact if hx : x.val ∈ p.S v then Sum.inl (p.terminal v ⟨x.val,hx⟩)
  else Sum.inr ⟨p.chosenEdge v x hx,
    p.transfer (p.chosenEdge v x hx) ⟨x.val,(p.chosenEdge_spec v x hx).2⟩⟩

def system : System Y V E I g where
  Input := fun v => p.U v
  src := p.src
  dst := p.dst
  step := p.step
  step_src := by
    intro v x e z h
    classical
    by_cases hx : x.val ∈ p.S v
    · simp only [step,dif_pos hx] at h
      cases h
    · have hh : (⟨p.chosenEdge v x hx,
          p.transfer (p.chosenEdge v x hx) ⟨x.val,(p.chosenEdge_spec v x hx).2⟩⟩ :
          (e : E) × p.U (p.dst e))=⟨e,z⟩ := by
        simpa only [step,dif_neg hx,Sum.inr.injEq] using h
      have he : p.chosenEdge v x hx=e := congrArg Sigma.fst hh
      rw [← he]
      exact (p.chosenEdge_spec v x hx).1
  ret := p.ret
  L := p.L
  lip := p.lip

@[simp] theorem step_stop (v : V) (x : p.U v) (hx : x.val ∈ p.S v) :
    p.system.step v x=Sum.inl (p.terminal v ⟨x.val,hx⟩) := by
  simp [system,step,hx]

theorem step_call (e : E) (x : p.D e) :
    p.system.step (p.src e) ⟨x.val,p.call_subset e x.property⟩=
      Sum.inr ⟨e,p.transfer e x⟩ := by
  have hx : x.val ∉ p.S (p.src e) := by
    intro hh
    exact Set.disjoint_left.1 (p.stop_disjoint (p.src e) e rfl) hh x.property
  let y : p.U (p.src e) := ⟨x.val,p.call_subset e x.property⟩
  have hchoice : p.chosenEdge (p.src e) y hx=e := by
    by_contra h
    exact Set.disjoint_left.1 (p.call_disjoint _ _ (p.chosenEdge_spec (p.src e) y hx).1 h)
      (p.chosenEdge_spec (p.src e) y hx).2 x.property
  change p.step (p.src e) y=_
  have hy : y.val ∉ p.S (p.src e) := hx
  rw [step,dif_neg hy]
  have hs : ∀ (f : E) (hmem : x.val ∈ p.D f), f=e →
      (⟨f,p.transfer f ⟨x.val,hmem⟩⟩ : (e : E) × p.U (p.dst e))=⟨e,p.transfer e x⟩ := by
    intro f hmem he
    subst f
    rfl
  exact congrArg Sum.inr (hs _ _ hchoice)

/-- The induced operator on subset domains has exactly the two clauses of the prompt. -/
theorem transform_clauses (F : p.system.Family) :
    (∀ v (x : p.S v), p.system.transform F v ⟨x.val,p.stop_subset v x.property⟩=p.terminal v x) ∧
    (∀ e (x : p.D e), p.system.transform F (p.src e) ⟨x.val,p.call_subset e x.property⟩=
      p.ret e (F (p.dst e) (p.transfer e x))) := by
  constructor
  · intro v x
    rw [System.transform,p.step_stop v ⟨x.val,p.stop_subset v x.property⟩ x.property]
  · intro e x; rw [System.transform,p.step_call]; rfl

end PartitionData
end MathGauge.RecursiveClosure
