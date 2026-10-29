import ConvexProjection

noncomputable section
open Filter Topology InnerProductSpace
namespace MathGauge.FiniteConstraints
variable {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The actual finite intersection, including the empty finite set. -/
def finite_meet (C : I → Set H) (F : Finset I) : Set H := ⋂ i ∈ F, C i

theorem finite_meet_mem (C : I → Set H) (F : Finset I) (x : H) :
    x ∈ finite_meet C F ↔ ∀ i ∈ F, x ∈ C i := by simp [finite_meet]

theorem finite_meet_closed (C : I → Set H) (hcl : ∀ i, IsClosed (C i)) (F : Finset I) :
    IsClosed (finite_meet C F) := isClosed_biInter (fun i _ => hcl i)

theorem finite_meet_convex (C : I → Set H) (hco : ∀ i, Convex ℝ (C i)) (F : Finset I) :
    Convex ℝ (finite_meet C F) := by
  intro x hx y hy a b ha hb hab
  simp only [finite_meet_mem] at hx hy ⊢
  exact fun i hi => hco i (hx i hi) (hy i hi) ha hb hab

theorem finite_meet_antitone (C : I → Set H) {F G : Finset I} (h : F ⊆ G) :
    finite_meet C G ⊆ finite_meet C F := by
  intro x hx
  simp only [finite_meet_mem] at hx ⊢
  exact fun i hi => hx i (h hi)

variable (C : I → Set H) (hcl : ∀ i, IsClosed (C i)) (hco : ∀ i, Convex ℝ (C i))
variable (B : ℝ) (hB : 0 ≤ B)
variable (hfeas : ∀ F : Finset I, ∃ z ∈ finite_meet C F, ‖z‖ ≤ B)

def finite_project (F : Finset I) (x : H) : H :=
  project (finite_meet C F) (by obtain ⟨z,hz,_⟩ := hfeas F; exact ⟨z,hz⟩)
    (finite_meet_closed C hcl F) (finite_meet_convex C hco F) x

theorem finite_project_mem (F : Finset I) (x : H) :
    finite_project C hcl hco B hfeas F x ∈ finite_meet C F :=
  (project_spec _ _ _ _ _).1

theorem finite_project_min (F : Finset I) (x z : H) (hz : z ∈ finite_meet C F) :
    ‖x - finite_project C hcl hco B hfeas F x‖ ≤ ‖x-z‖ :=
  project_min _ _ _ _ _ _ hz

theorem finite_project_bound (F : Finset I) (x : H) :
    ‖x-finite_project C hcl hco B hfeas F x‖ ≤ ‖x‖+B := by
  obtain ⟨z,hz,hzb⟩ := hfeas F
  exact (finite_project_min C hcl hco B hfeas F x z hz).trans
    ((norm_sub_le x z).trans (add_le_add_right hzb _))

def energy (x : H) (F : Finset I) : ℝ := ‖x-finite_project C hcl hco B hfeas F x‖^2

theorem energy_mono (x : H) : Monotone (energy C hcl hco B hfeas x) := by
  intro F G hFG
  have h := finite_project_min C hcl hco B hfeas F x
    (finite_project C hcl hco B hfeas G x)
    (finite_meet_antitone C hFG (finite_project_mem C hcl hco B hfeas G x))
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem energy_bdd (x : H) : BddAbove (Set.range (energy C hcl hco B hfeas x)) := by
  refine ⟨(‖x‖+B)^2, ?_⟩
  rintro r ⟨F,rfl⟩
  exact pow_le_pow_left₀ (norm_nonneg _) (finite_project_bound C hcl hco B hfeas F x) 2

theorem finite_nested_energy (x : H) {F G : Finset I} (hFG : F ⊆ G) :
    ‖finite_project C hcl hco B hfeas F x-finite_project C hcl hco B hfeas G x‖^2 ≤
      energy C hcl hco B hfeas x G - energy C hcl hco B hfeas x F :=
  project_energy _ _ _ _ _ _
    (finite_meet_antitone C hFG (finite_project_mem C hcl hco B hfeas G x))

/-- Cauchy for the full finite-subset directed net; the index type is unrestricted. -/
theorem finite_project_cauchy (x : H) :
    CauchySeq (fun F : Finset I => finite_project C hcl hco B hfeas F x) := by
  classical
  rw [Metric.cauchySeq_iff]
  intro ε hε
  let L := ⨆ F, energy C hcl hco B hfeas x F
  have hb := energy_bdd C hcl hco B hfeas x
  have hg : L-(ε/2)^2 < L := by nlinarith
  obtain ⟨F₀,hF₀⟩ := exists_lt_of_lt_ciSup hg
  refine ⟨F₀, ?_⟩
  intro F hF G hG
  have hub (D : Finset I) : energy C hcl hco B hfeas x D ≤ L := le_ciSup hb D
  have hlowF := energy_mono C hcl hco B hfeas x hF
  have hlowG := energy_mono C hcl hco B hfeas x hG
  have heF := finite_nested_energy C hcl hco B hfeas x (Finset.subset_union_left (s₁ := F) (s₂ := G))
  have heG := finite_nested_energy C hcl hco B hfeas x (Finset.subset_union_right (s₁ := F) (s₂ := G))
  have hF' : ‖finite_project C hcl hco B hfeas F x-
      finite_project C hcl hco B hfeas (F∪G) x‖ < ε/2 := by
    nlinarith [hub (F∪G), norm_nonneg (finite_project C hcl hco B hfeas F x-
      finite_project C hcl hco B hfeas (F∪G) x)]
  have hG' : ‖finite_project C hcl hco B hfeas G x-
      finite_project C hcl hco B hfeas (F∪G) x‖ < ε/2 := by
    nlinarith [hub (F∪G), norm_nonneg (finite_project C hcl hco B hfeas G x-
      finite_project C hcl hco B hfeas (F∪G) x)]
  rw [dist_eq_norm]
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (finite_project C hcl hco B hfeas F x)
    (finite_project C hcl hco B hfeas (F∪G) x)
    (finite_project C hcl hco B hfeas G x)
  rw [norm_sub_rev (finite_project C hcl hco B hfeas (F∪G) x)] at ht
  linarith

/-- Completeness yields a genuine common point and a minimizer, not only separate finite witnesses. -/
theorem exists_global_limit (x : H) : ∃ p : H,
    (∀ i, p ∈ C i) ∧
    Tendsto (fun F : Finset I => finite_project C hcl hco B hfeas F x) atTop (𝓝 p) ∧
    (∀ z, (∀ i, z ∈ C i) → ‖x-p‖ ≤ ‖x-z‖) := by
  classical
  obtain ⟨p,hp⟩ := cauchySeq_tendsto_of_complete (finite_project_cauchy C hcl hco B hfeas x)
  have hmem : ∀ i, p ∈ C i := by
    intro i
    apply (hcl i).mem_of_tendsto hp
    filter_upwards [eventually_ge_atTop ({i} : Finset I)] with F hF
    exact (finite_meet_mem C F _).1 (finite_project_mem C hcl hco B hfeas F x) i
      (hF (by simp))
  refine ⟨p,hmem,hp,?_⟩
  intro z hz
  apply le_of_tendsto (tendsto_const_nhds.sub hp).norm
  exact Eventually.of_forall (fun F => finite_project_min C hcl hco B hfeas F x z
    ((finite_meet_mem C F z).2 (fun i _ => hz i)))

include hcl hco B hfeas in
theorem global_nonempty : (⋂ i, C i).Nonempty := by
  obtain ⟨p,hp,_,_⟩ := exists_global_limit C hcl hco B hfeas (0 : H)
  exact ⟨p, by simpa using hp⟩

def global_project (x : H) : H := project (⋂ i, C i)
  (global_nonempty C hcl hco B hfeas) (isClosed_iInter hcl) (convex_iInter hco) x

theorem finite_project_tendsto (x : H) :
    Tendsto (fun F : Finset I => finite_project C hcl hco B hfeas F x) atTop
      (𝓝 (global_project C hcl hco B hfeas x)) := by
  obtain ⟨p,hp,ht,hm⟩ := exists_global_limit C hcl hco B hfeas x
  have he : p = global_project C hcl hco B hfeas x := by
    apply project_unique
    · simpa using hp
    · intro z hz
      exact hm z (by simpa using hz)
  exact he ▸ ht

theorem global_mem (x : H) : ∀ i, global_project C hcl hco B hfeas x ∈ C i := by
  have h := (project_spec (⋂ i, C i) (global_nonempty C hcl hco B hfeas)
    (isClosed_iInter hcl) (convex_iInter hco) x).1
  simpa using h

theorem global_energy_error (x : H) (F : Finset I) :
    ‖finite_project C hcl hco B hfeas F x-global_project C hcl hco B hfeas x‖^2 ≤
      ‖x-global_project C hcl hco B hfeas x‖^2 - energy C hcl hco B hfeas x F := by
  apply project_energy
  exact (finite_meet_mem C F _).2 (fun i _ => global_mem C hcl hco B hfeas x i)

theorem global_energy_eq_sup (x : H) :
    ‖x-global_project C hcl hco B hfeas x‖^2 = ⨆ F, energy C hcl hco B hfeas x F := by
  exact tendsto_nhds_unique ((tendsto_const_nhds.sub
    (finite_project_tendsto C hcl hco B hfeas x)).norm.pow 2)
    (tendsto_atTop_ciSup (energy_mono C hcl hco B hfeas x)
      (energy_bdd C hcl hco B hfeas x))

theorem global_nonexpansive (x y : H) :
    ‖global_project C hcl hco B hfeas x-global_project C hcl hco B hfeas y‖ ≤ ‖x-y‖ :=
  project_nonexpansive _ _ _ _ x y

theorem global_unique (x z : H) (hz : ∀ i, z ∈ C i)
    (hm : ∀ w, (∀ i, w ∈ C i) → ‖x-z‖ ≤ ‖x-w‖) :
    z = global_project C hcl hco B hfeas x := by
  apply project_unique
  · simpa using hz
  · intro w hw
    exact hm w (by simpa using hw)

theorem finite_empty (x : H) : finite_project C hcl hco B hfeas ∅ x=x := by
  symm
  apply project_unique
  · simp [finite_meet]
  · intro w hw
    simp

theorem global_empty [IsEmpty I] (x : H) : global_project C hcl hco B hfeas x=x := by
  symm
  apply global_unique C hcl hco B hfeas
  · intro i; exact isEmptyElim i
  · intro w hw
    simp

end MathGauge.FiniteConstraints
