import MathGauge.C003.Completeness

namespace MathGauge.C003

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open formal_oet.vol_01.ch_03_operator_local_degeneracy

noncomputable section

variable {X I : Type} {bot : X}

/-- Forward image centers remain internal and their cardinality cannot increase. -/
theorem pushforward_internal_cover (d₁ d₂ : X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (r s : ENNReal) (S : Finset X)
    (hnet : InternalEpsilonNet d₁ r U S)
    (htransfer : ∀ x ∈ U, ∀ y ∈ U, d₁ x y < r → d₂ (φ.func x) (φ.func y) < s) :
    ∃ T : Finset X, InternalEpsilonNet d₂ s (φ.func '' U) T ∧ T.card ≤ S.card := by
  classical
  refine ⟨S.image φ.func, ⟨?_,?_⟩,Finset.card_image_le⟩
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨x,hx,rfl⟩
    exact Set.mem_image_of_mem _ (hnet.1 hx)
  · rintro z ⟨x,hx,rfl⟩
    obtain ⟨c,hc,hd⟩ := hnet.2 x hx
    exact ⟨φ.func c,Finset.mem_image_of_mem _ hc,htransfer x hx c (hnet.1 hc) hd⟩

/-- Each internal output center has an input representative; choice never leaves the input set. -/
theorem pullback_internal_cover (d₁ d₂ : X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (r s : ENNReal) (T : Finset X)
    (hnet : InternalEpsilonNet d₂ s (φ.func '' U) T)
    (htransfer : ∀ x ∈ U, ∀ y ∈ U, d₂ (φ.func x) (φ.func y) < s → d₁ x y < r) :
    ∃ S : Finset X, InternalEpsilonNet d₁ r U S ∧ S.card ≤ T.card := by
  classical
  have hex : ∀ z ∈ T, ∃ x ∈ U, φ.func x = z := fun z hz => hnet.1 hz
  let pre (z : {z // z ∈ T}) : X := Classical.choose (hex z.val z.prop)
  have hp (z : {z // z ∈ T}) : pre z ∈ U ∧ φ.func (pre z) = z.val :=
    Classical.choose_spec (hex z.val z.prop)
  refine ⟨T.attach.image pre,⟨?_,?_⟩,?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨z,_,rfl⟩
    exact (hp z).1
  · intro x hx
    obtain ⟨z,hz,hd⟩ := hnet.2 (φ.func x) (Set.mem_image_of_mem _ hx)
    refine ⟨pre ⟨z,hz⟩,Finset.mem_image_of_mem _ (Finset.mem_attach _ _),?_⟩
    apply htransfer x hx _ (hp ⟨z,hz⟩).1
    simpa only [(hp ⟨z,hz⟩).2] using hd
  · exact (Finset.card_image_le).trans_eq Finset.card_attach

/-- OET anchor: h-5f1e227b06f3a2d1. The exact epsilon/L input cover is transported. -/
theorem lip_cover_transport (d : I → X → X → ENNReal) (φ : Operator X bot)
    (U : Set X) (i j : I) (L ε : ENNReal) (hL : 0 < L) (hfin : L ≠ ⊤)
    (hlip : ∀ x ∈ U, ∀ y ∈ U, d j (φ.func x) (φ.func y) ≤ L * d i x y)
    (S : Finset X) (hnet : InternalEpsilonNet (d i) (ε/L) U S) :
    ∃ T : Finset X, InternalEpsilonNet (d j) ε (φ.func '' U) T ∧ T.card ≤ S.card := by
  apply pushforward_internal_cover (d i) (d j) φ U (ε/L) ε S hnet
  intro x hx y hy hd
  have hmul : L * (ε/L) = ε :=
    ENNReal.mul_div_cancel' (fun h => ((ne_of_gt hL) h).elim) (fun h => (hfin h).elim)
  exact lt_of_le_of_lt (hlip x hx y hy)
    (hmul ▸ ENNReal.mul_lt_mul_right (ne_of_gt hL) hfin hd)

/-- OET anchor: h-9d16603c422d3b11. A positive finite matrix entry pulls output covers back. -/
theorem colip_cover_transport [Fintype I] (d : I → X → X → ENNReal)
    (φ : Operator X bot) (U : Set X) (i j : I) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d φ U K) (hpos : 0 < K i j) (hfin : K i j ≠ ⊤)
    (ε : ENNReal) (T : Finset X) (hnet : InternalEpsilonNet (d j) ε (φ.func '' U) T) :
    ∃ S : Finset X, InternalEpsilonNet (d i) (ε / K i j) U S ∧ S.card ≤ T.card := by
  apply pullback_internal_cover (d i) (d j) φ U (ε / K i j) ε T hnet
  intro x hx y hy hd
  have hpoint : K i j * d i x y ≤ d j (φ.func x) (φ.func y) :=
    (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y))
      (Finset.mem_univ i)).trans (hK.2.2 x hx y hy j)
  have hmul : K i j * (ε / K i j) = ε :=
    ENNReal.mul_div_cancel' (fun h => ((ne_of_gt hpos) h).elim) (fun h => (hfin h).elim)
  apply (ENNReal.mul_lt_mul_iff_right (ne_of_gt hpos) hfin).mp
  rw [hmul]
  exact lt_of_le_of_lt hpoint hd

/-- OET anchor: h-9ecc7d0b4b541992. Zero-radius transport also handles the empty subset. -/
theorem zero_radius_cover_transport (d : I → X → X → ENNReal)
    (φ : Operator X bot) (A B : Set X) (hBA : B ⊆ A) (i j : I)
    (τ ε : ENNReal) (hε : 0 < ε)
    (hτ : τ ≤ min_annihilation_radius d φ i (singleton_nonempty_finset j) A)
    (S : Finset X) (hnet : InternalEpsilonNet (d i) τ B S) :
    ∃ T : Finset X, InternalEpsilonNet (d j) ε (φ.func '' B) T ∧ T.card ≤ S.card := by
  apply pushforward_internal_cover (d i) (d j) φ B τ ε S hnet
  intro x hx y hy hxy
  rw [zero_of_lt_min_annihilation_radius d φ A i j y x τ hτ (hBA hy) (hBA hx) hxy]
  exact hε

theorem finite_positive_covering_entropy_is_real (dist : X → X → ENNReal)
    (U : Set X) (ε : ENNReal) (hne : U.Nonempty)
    (hfinite : covering_number dist ε U < ⊤) :
    (1 : ENNReal) ≤ covering_number dist ε U ∧
      ∃ e : ℝ, metric_entropy dist ε U = (e : EReal) := by
  have hpos := one_le_covering_number_of_nonempty dist ε U hne
  refine ⟨hpos,Real.logb 2 (covering_number dist ε U).toReal,?_⟩
  simp [metric_entropy,log2_ereal,ne_of_lt hfinite,
    ne_of_gt (lt_of_lt_of_le zero_lt_one hpos)]

/-- OET anchor: h-f4a4cb93f576325e. Both subfamily entropies are finite real values. -/
theorem finite_subfamily_entropies_are_real [Fintype I]
    (d : I → X → X → ENNReal) (hd : ∀ i x, d i x x = 0)
    (φ : Operator X bot) (U : Set X) (hU : U.Nonempty) (hdom : U ⊆ dom φ)
    (hfin : U.Finite) (Jin Jout : NonemptyFinset I) (ε : ENNReal)
    (hε : 0 < ε) (hεfin : ε ≠ ⊤) :
    (1 : ENNReal) ≤ cov_num_comp d Jin ε U ∧ cov_num_comp d Jin ε U < ⊤ ∧
    (1 : ENNReal) ≤ cov_num_comp d Jout ε (φ.func '' U) ∧
    cov_num_comp d Jout ε (φ.func '' U) < ⊤ ∧
    (∃ a b : ℝ, metric_entropy (comp_pseudo_metric d Jin) ε U = (a : EReal) ∧
      metric_entropy (comp_pseudo_metric d Jout) ε (φ.func '' U) = (b : EReal)) ∧
    SubfamilyEntropyDiffWellDefined d φ U Jin Jout ε := by
  have hv := finite_set_subfamily_mapping_entropy_diff_well_defined d φ U Jin Jout ε
    hU hdom hfin hε hεfin hd
  have ha := finite_positive_covering_entropy_is_real (comp_pseudo_metric d Jin) U ε hU hv.1
  have hb := finite_positive_covering_entropy_is_real (comp_pseudo_metric d Jout)
    (φ.func '' U) ε (hU.image _) hv.2.1
  rcases ha.2 with ⟨a,hae⟩; rcases hb.2 with ⟨b,hbe⟩
  exact ⟨ha.1,hv.1,hb.1,hv.2.1,⟨a,b,hae,hbe⟩,hv.2.2⟩

end
end MathGauge.C003
