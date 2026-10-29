import CyclicPotential
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Topology.UniformSpace.Dini
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section
open Filter Topology
namespace MathGauge.FinitePotentials
open MathGauge.CyclicPotential
variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

 theorem potential_mono {Γ Δ : Set (E × (E →L[ℝ] ℝ))} (h : Γ⊆Δ)
    (a : E × (E →L[ℝ] ℝ)) (x : E) : potential Γ a x≤potential Δ a x := by
  apply iSup_le
  intro p
  exact path_le_potential Δ a ⟨p.val,fun b hb => h (p.property b hb)⟩ x

 theorem cyclic_mono {Γ Δ : Set (E × (E →L[ℝ] ℝ))} (h : Γ⊆Δ) (hΔ : CyclicMonotone Δ) :
    CyclicMonotone Γ := fun a ha l hl => hΔ a (h ha) l (fun b hb => h (hl b hb))

 def finiteGraph (Γ : Set (E × (E →L[ℝ] ℝ))) (a : Γ) (s : Finset Γ) : Set (E × (E →L[ℝ] ℝ)) :=
  {r | r=a.val ∨ ∃ hr : r∈Γ,(⟨r,hr⟩ : Γ)∈s}

 theorem finiteGraph_subset (Γ : Set (E × (E →L[ℝ] ℝ))) (a : Γ) (s : Finset Γ) :
    finiteGraph Γ a s⊆Γ := by
  rintro r (rfl|⟨hr,_⟩)
  · exact a.property
  · exact hr

 theorem base_mem_finiteGraph (Γ : Set (E × (E →L[ℝ] ℝ))) (a : Γ) (s : Finset Γ) :
    a.val∈finiteGraph Γ a s := Or.inl rfl

 theorem finiteGraph_finite (Γ : Set (E × (E →L[ℝ] ℝ))) (a : Γ) (s : Finset Γ) :
    (finiteGraph Γ a s).Finite := by
  have he : finiteGraph Γ a s={a.val}∪(Subtype.val '' (s : Set Γ)) := by
    ext r
    simp only [finiteGraph,Set.mem_setOf_eq,Set.mem_union,Set.mem_singleton_iff,Set.mem_image]
    constructor
    · rintro (h|⟨hr,hs⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨r,hr⟩,hs,rfl⟩
    · rintro (h|⟨r,hs,rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨r.property,hs⟩
  rw [he]
  exact (Set.finite_singleton _).union (s.finite_toSet.image _)

 theorem finiteGraph_mono (Γ : Set (E × (E →L[ℝ] ℝ))) (a : Γ) : Monotone (finiteGraph Γ a) := by
  intro s t h r hr
  rcases hr with hr|⟨hr,hs⟩
  · exact Or.inl hr
  · exact Or.inr ⟨hr,h hs⟩

 theorem every_finite_subgraph (Γ : Set (E × (E →L[ℝ] ℝ))) (a : Γ)
    (Λ : Set (E × (E →L[ℝ] ℝ))) (hΛ : Λ.Finite) (hsub : Λ⊆Γ) (ha : a.val∈Λ) :
    ∃ s : Finset Γ,finiteGraph Γ a s=Λ := by
  classical
  let t : Set Γ := Subtype.val ⁻¹' Λ
  have ht : t.Finite := hΛ.preimage Subtype.val_injective.injOn
  refine ⟨ht.toFinset,?_⟩
  ext r
  constructor
  · rintro (rfl|⟨hr,hs⟩)
    · exact ha
    · simpa only [Set.Finite.mem_toFinset,t,Set.mem_preimage] using hs
  · intro hr
    exact Or.inr ⟨hsub hr,by simpa only [Set.Finite.mem_toFinset,t,Set.mem_preimage] using hr⟩

 theorem potential_finite_sup (Γ : Set (E × (E →L[ℝ] ℝ))) (a : Γ) (x : E) :
    potential Γ a.val x=⨆ s : Finset Γ,potential (finiteGraph Γ a s) a.val x := by
  classical
  apply le_antisymm
  · apply iSup_le
    intro p
    let s : Finset Γ := (p.val.attach.map (fun b => (⟨b.val,p.property b.val b.property⟩ : Γ))).toFinset
    apply le_trans (path_le_potential (finiteGraph Γ a s) a.val ⟨p.val,?_⟩ x)
      (le_iSup (fun s : Finset Γ => potential (finiteGraph Γ a s) a.val x) s)
    intro b hb
    apply Or.inr
    refine ⟨p.property b hb,?_⟩
    simp only [s,List.mem_toFinset,List.mem_map,List.mem_attach,true_and]
    exact ⟨⟨b,hb⟩,rfl⟩
  · exact iSup_le (fun s => potential_mono (finiteGraph_subset Γ a s) a.val x)

section Normed
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

 theorem path_difference_bound (a : H × (H →L[ℝ] ℝ))
    (l : List (H × (H →L[ℝ] ℝ))) (M : ℝ) (ha : ‖a.2‖≤M)
    (hl : ∀ b∈l,‖b.2‖≤M) (x y : H) :
    |path_value a l x-path_value a l y|≤M*‖x-y‖ := by
  induction l generalizing a with
  | nil =>
    have he : a.2 (x-a.1)-a.2 (y-a.1)=a.2 (x-y) := by
      simp only [map_sub];ring
    simpa only [path_value,he,Real.norm_eq_abs] using
      (a.2.le_opNorm (x-y)).trans (mul_le_mul_of_nonneg_right ha (norm_nonneg _))
  | cons b l ih =>
    simpa only [path_value,add_sub_add_left_eq_sub] using
      ih b (hl b (by simp)) (fun c hc => hl c (by simp [hc]))

 theorem finite_potential_finite (Γ : Set (H × (H →L[ℝ] ℝ))) (hΓ : CyclicMonotone Γ)
    (hfin : Γ.Finite) (a : H × (H →L[ℝ] ℝ)) (ha : a∈Γ) (x : H) :
    potential Γ a x≠⊤ := by
  obtain ⟨M,hM⟩ := (hfin.image (fun b => ‖b.2‖)).bddAbove
  have hb (b : H × (H →L[ℝ] ℝ)) (hb : b∈Γ) : ‖b.2‖≤M := hM ⟨b,hb,rfl⟩
  apply ne_top_of_le_ne_top (EReal.coe_ne_top (M*‖x-a.1‖))
  rw [potential_le_real_iff]
  intro p
  have hd := (le_abs_self (path_value a p.val x-path_value a p.val a.1)).trans
    (path_difference_bound a p.val M (hb a ha) (fun b h => hb b (p.property b h)) x a.1)
  have hc := hΓ a ha p.val p.property
  linarith

 def realPotential (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ)) (x : H) : ℝ :=
   (potential Γ a x).toReal

 theorem realPotential_coe (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ))
    (hf : ∀ x,potential Γ a x≠⊤) (x : H) :
    (realPotential Γ a x : EReal)=potential Γ a x :=
  EReal.coe_toReal (hf x) (potential_ne_bot Γ a x)

 theorem realPotential_convex (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ))
    (hf : ∀ x,potential Γ a x≠⊤) : ConvexOn ℝ Set.univ (realPotential Γ a) := by
  refine ⟨convex_univ,?_⟩
  intro x hx y hy s t hs ht hst
  have h := potential_epigraph_convex Γ a
    (show (x,realPotential Γ a x)∈real_epigraph (potential Γ a) by
      change potential Γ a x≤(realPotential Γ a x : EReal);rw [realPotential_coe Γ a hf])
    (show (y,realPotential Γ a y)∈real_epigraph (potential Γ a) by
      change potential Γ a y≤(realPotential Γ a y : EReal);rw [realPotential_coe Γ a hf]) hs ht hst
  change potential Γ a (s • x+t • y)≤((s*realPotential Γ a x+t*realPotential Γ a y : ℝ) : EReal) at h
  rw [← realPotential_coe Γ a hf] at h
  exact EReal.coe_le_coe_iff.mp h

 theorem realPotential_continuous [FiniteDimensional ℝ H]
    (Γ : Set (H × (H →L[ℝ] ℝ))) (a : H × (H →L[ℝ] ℝ))
    (hf : ∀ x,potential Γ a x≠⊤) : Continuous (realPotential Γ a) :=
  continuousOn_univ.mp ((realPotential_convex Γ a hf).continuousOn isOpen_univ)

 theorem finite_net_uniform [FiniteDimensional ℝ H]
    (Γ : Set (H × (H →L[ℝ] ℝ))) (hΓ : CyclicMonotone Γ) (a : Γ)
    (hf : ∀ x,potential Γ a.val x≠⊤) (K : Set H) (hK : IsCompact K) :
    TendstoUniformlyOn (fun s : Finset Γ => realPotential (finiteGraph Γ a s) a.val)
      (realPotential Γ a.val) atTop K := by
  have hfinite (s : Finset Γ) (x : H) : potential (finiteGraph Γ a s) a.val x≠⊤ :=
    finite_potential_finite _ (cyclic_mono (finiteGraph_subset Γ a s) hΓ)
      (finiteGraph_finite Γ a s) a.val (base_mem_finiteGraph Γ a s) x
  have hmono (x : H) : Monotone (fun s : Finset Γ => realPotential (finiteGraph Γ a s) a.val x) := by
    intro s t h
    apply EReal.coe_le_coe_iff.mp
    rw [realPotential_coe _ _ (hfinite s),realPotential_coe _ _ (hfinite t)]
    exact potential_mono (finiteGraph_mono Γ a h) a.val x
  have hle (x : H) (s : Finset Γ) :
      realPotential (finiteGraph Γ a s) a.val x≤realPotential Γ a.val x := by
    apply EReal.coe_le_coe_iff.mp
    rw [realPotential_coe _ _ (hfinite s),realPotential_coe _ _ hf]
    exact potential_mono (finiteGraph_subset Γ a s) a.val x
  have hsup (x : H) :
      (⨆ s : Finset Γ,realPotential (finiteGraph Γ a s) a.val x)=realPotential Γ a.val x := by
    apply le_antisymm
    · exact ciSup_le (hle x)
    · by_contra hn
      have hl : (⨆ s : Finset Γ,realPotential (finiteGraph Γ a s) a.val x)<realPotential Γ a.val x := lt_of_not_ge hn
      have hb : BddAbove (Set.range (fun s : Finset Γ => realPotential (finiteGraph Γ a s) a.val x)) :=
        ⟨realPotential Γ a.val x,by rintro _ ⟨s,rfl⟩;exact hle x s⟩
      have he : potential Γ a.val x≤(((⨆ s : Finset Γ,realPotential (finiteGraph Γ a s) a.val x) : ℝ) : EReal) := by
        rw [potential_finite_sup Γ a x]
        apply iSup_le
        intro s
        rw [← realPotential_coe _ _ (hfinite s)]
        exact EReal.coe_le_coe (le_ciSup hb s)
      rw [← realPotential_coe Γ a.val hf] at he
      exact (not_le_of_gt hl) (EReal.coe_le_coe_iff.mp he)
  apply Monotone.tendstoUniformlyOn_of_forall_tendsto hK
    (fun s => (realPotential_continuous _ _ (hfinite s)).continuousOn)
    (fun x _ => hmono x) (realPotential_continuous Γ a.val hf).continuousOn
  intro x hx
  rw [← hsup x]
  exact tendsto_atTop_ciSup (hmono x) (⟨_,by rintro _ ⟨s,rfl⟩;exact hle x s⟩)

end Normed
end MathGauge.FinitePotentials
