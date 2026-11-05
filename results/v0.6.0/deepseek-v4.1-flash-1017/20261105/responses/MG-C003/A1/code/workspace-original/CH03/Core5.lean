import CH03.Core4

namespace formal_oet.vol_01.ch_03_operator_local_degeneracy
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set

variable {X : Type} {I : Type} {bot : X}

/-! ## Entropy difference for constant/id components (Proposition 3.18) -/

theorem subfamily_pseudometric_eq_zero_of_const
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (J : Set I) (hJ : J ⊆ Iconst d φ U) :
    ∀ x ∈ φ.func '' U, ∀ y ∈ φ.func '' U,
      subfamily_pseudometric d J x y = 0 := by
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
  rw [subfamily_pseudometric, ENNReal.iSup_eq_zero]
  intro j
  exact hJ j.2 a ha b hb

theorem subfamily_metric_entropy_const
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (J : Set I) (hJne : J.Nonempty) (hJ : J ⊆ Iconst d φ U)
    (hU : U.Nonempty) (ε : ENNReal) (hε : 0 < ε) :
    covering_number (subfamily_pseudometric d J) ε (φ.func '' U) = 1 ∧
      subfamily_metric_entropy d J ε (φ.func '' U) = 0 := by
  have hne : (φ.func '' U).Nonempty := by
    rcases hU with ⟨x, hx⟩
    exact ⟨φ.func x, ⟨x, hx, rfl⟩⟩
  have hcover : covering_number (subfamily_pseudometric d J) ε (φ.func '' U) = 1 :=
    covering_number_eq_one_of_forall_zero _ _ hne ε hε
      (subfamily_pseudometric_eq_zero_of_const d φ U J hJ)
  refine ⟨hcover, ?_⟩
  unfold subfamily_metric_entropy
  simp [hcover, log2_ereal]

theorem const_channel_entropy_diff
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (Jin Jout : Set I) (hJoutne : Jout.Nonempty)
    (hJout : Jout ⊆ Iconst d φ U) (hU : U.Nonempty)
    (ε : ENNReal) (hε : 0 < ε) :
    covering_number (subfamily_pseudometric d Jout) ε (φ.func '' U) = 1 ∧
      subfamily_metric_entropy d Jout ε (φ.func '' U) = 0 ∧
      mappingEntropyDiff d φ U Jin Jout ε =
        subfamily_metric_entropy d Jin ε U := by
  obtain ⟨hc, he⟩ := subfamily_metric_entropy_const d φ U Jout hJoutne hJout hU ε hε
  refine ⟨hc, he, ?_⟩
  have hnonbot : subfamily_metric_entropy d Jin ε U ≠ ⊥ :=
    metric_entropy_ne_bot_of_nonempty (subfamily_pseudometric d Jin) U hU ε
  unfold mappingEntropyDiff
  rw [he]
  exact erealSub_eq_self_of_right_zero hnonbot

/-! ## Isometric image covering and identity channels -/

theorem image_net_of_isometry [DecidableEq X]
    (d : X → X → ENNReal) (φ : Operator X bot) (U : Set X) {ε : ENNReal}
    (hiso : ∀ x ∈ U, ∀ y ∈ U, d (φ.func x) (φ.func y) = d x y)
    {S : Finset X} (hS : InternalEpsilonNet d ε U S) :
    InternalEpsilonNet d ε (φ.func '' U) (S.image φ.func) := by
  classical
  constructor
  · intro z hz
    rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
    exact ⟨s, hS.1 hs, rfl⟩
  · intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    rcases hS.2 x hx with ⟨s, hs, hdist⟩
    refine ⟨φ.func s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ?_⟩
    rwa [hiso x hx s (hS.1 hs)]

theorem preimage_net_of_isometry
    (d : X → X → ENNReal) (φ : Operator X bot) (U : Set X) {ε : ENNReal}
    (hiso : ∀ x ∈ U, ∀ y ∈ U, d (φ.func x) (φ.func y) = d x y)
    {T : Finset X} (hT : InternalEpsilonNet d ε (φ.func '' U) T) :
    ∃ S : Finset X, InternalEpsilonNet d ε U S ∧ S.card ≤ T.card := by
  classical
  let rep : {t : X // t ∈ T} → X := fun t =>
    Classical.choose (hT.1 t.2)
  have hrepU : ∀ t : {t : X // t ∈ T}, rep t ∈ U := fun t =>
    (Classical.choose_spec (hT.1 t.2)).1
  have hrepval : ∀ t : {t : X // t ∈ T}, φ.func (rep t) = t.1 := fun t =>
    (Classical.choose_spec (hT.1 t.2)).2
  let S : Finset X := T.attach.image rep
  refine ⟨S, ?_, ?_⟩
  · constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨t, _, rfl⟩
      exact hrepU t
    · intro x hx
      rcases hT.2 (φ.func x) ⟨x, hx, rfl⟩ with ⟨t, ht, hdist⟩
      refine ⟨rep ⟨t, ht⟩, ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟨t, ht⟩, Finset.mem_attach _ _, rfl⟩
      · have hval : φ.func (rep ⟨t, ht⟩) = t := hrepval ⟨t, ht⟩
        have hdist' : d (φ.func x) (φ.func (rep ⟨t, ht⟩)) < ε := by
          simpa [hval] using hdist
        simpa [hiso x hx (rep ⟨t, ht⟩) (hrepU ⟨t, ht⟩)] using hdist' 
  · calc
      S.card ≤ T.attach.card := Finset.card_image_le
      _ = T.card := Finset.card_attach

theorem covering_number_image_eq_of_isometry
    (d : X → X → ENNReal) (φ : Operator X bot) (U : Set X) (ε : ENNReal)
    (hiso : ∀ x ∈ U, ∀ y ∈ U, d (φ.func x) (φ.func y) = d x y) :
    covering_number d ε (φ.func '' U) = covering_number d ε U := by
  classical
  apply le_antisymm
  · by_cases hfin : ∃ S : Finset X, InternalEpsilonNet d ε U S
    · obtain ⟨S, hS, hcover, _⟩ := covering_number_attained d ε U hfin
      calc
        covering_number d ε (φ.func '' U) ≤ (S.image φ.func).card :=
          covering_number_le_card_of_net (image_net_of_isometry d φ U hiso hS)
        _ ≤ (S.card : ENNReal) := by exact_mod_cast Finset.card_image_le
        _ = covering_number d ε U := hcover.symm
    · rw [(covering_number_eq_top_iff d ε U).mpr hfin]
      exact le_top
  · by_cases hfin : ∃ T : Finset X, InternalEpsilonNet d ε (φ.func '' U) T
    · obtain ⟨T, hT, hcover, _⟩ := covering_number_attained d ε (φ.func '' U) hfin
      obtain ⟨S, hS, hcard⟩ := preimage_net_of_isometry d φ U hiso hT
      calc
        covering_number d ε U ≤ S.card := covering_number_le_card_of_net hS
        _ ≤ (T.card : ENNReal) := by exact_mod_cast hcard
        _ = covering_number d ε (φ.func '' U) := hcover.symm
    · rw [(covering_number_eq_top_iff d ε (φ.func '' U)).mpr hfin]
      exact le_top

theorem id_channel_covering_eq
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (j : I) (hj : j ∈ Iid d φ U)
    (ε : ENNReal) :
    covering_number (d j) ε (φ.func '' U) = covering_number (d j) ε U := by
  classical
  exact covering_number_image_eq_of_isometry (d j) φ U ε
    (id_component_isometry d hd φ U j hj)

theorem id_channel_entropy_eq
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (j : I) (hj : j ∈ Iid d φ U)
    (ε : ENNReal) :
    subfamily_metric_entropy d ({j} : Set I) ε (φ.func '' U) =
      subfamily_metric_entropy d ({j} : Set I) ε U := by
  rw [subfamily_metric_entropy_singleton, subfamily_metric_entropy_singleton]
  unfold metric_entropy
  rw [id_channel_covering_eq d hd φ U j hj ε]

theorem id_channel_entropy_diff_zero
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (φ : Operator X bot) (U : Set X) (j : I) (hj : j ∈ Iid d φ U)
    (ε : ENNReal) (hdef : MappingEntropyDiffWellDefined d φ U {j} {j} ε) :
    mappingEntropyDiff d φ U {j} {j} ε = 0 := by
  unfold mappingEntropyDiff
  rw [id_channel_entropy_eq d hd φ U j hj ε]
  exact erealSub_self _

end formal_oet.vol_01.ch_03_operator_local_degeneracy
