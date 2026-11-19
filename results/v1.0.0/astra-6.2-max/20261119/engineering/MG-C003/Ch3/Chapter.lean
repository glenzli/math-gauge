import Ch3.Correspondence
import Ch3.Step
import Ch3.Readout
import Ch3.Floor
import Ch3.Rearrange

namespace MG
open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
section
variable {X I : Type} {b : X} {f g : Op b} {U A B : Set X} {d : I → Dist X}

theorem subfamilyConstant (_hU : U.Nonempty) (_hu : U ⊆ dom f) {J : Set I} (_hj : J.Nonempty)
    (hc : J ⊆ constSet d f U) (i : I) :
    (∀ y ∈ U, fiber (subdist d J) f U (f.func y) = U ∧ radius (d i) (subdist d J) f U y = ⊤) ∧
    uniform (d i) (subdist d J) f U U = ⊤ := by
  have h : ∀ j ∈ J, Const (d j) f U := fun _ hj => hc hj
  have hr := constRadii (d i) (constSub d h)
  exact ⟨fun _ hy => ⟨constSubFiber d h hy,hr.1 _ hy⟩,hr.2⟩

theorem subfamilyPartition (m : ∀ i, ExtendedPseudoMetric X b (d i)) (J : Set I) (hJ : J.Nonempty)
    (_hu : U ⊆ dom f) :
    (∀ F ∈ blocks (subdist d J) f U, F.Nonempty) ∧ ⋃₀ (blocks (subdist d J) f U) = U ∧
    (blocks (subdist d J) f U).PairwiseDisjoint id :=
  blockPartition (subfamily_pseudometric_is_extended d J hJ m)

theorem compositeBounds [Fintype I] (i j l : I) (_hn : U.Nonempty) (hu : U ⊆ dom (g*f)) :
    U ⊆ dom f ∧ f.func '' U ⊆ dom g ∧
    ((∀ a ∈ f.func '' U, ∀ c ∈ f.func '' U, d l a c = 0 → d j (g.func a) (g.func c) = 0) →
      matrix d f U l i ≤ matrix d (g*f) U j i) ∧
    (∀ L, positiveFinite L → (∀ x ∈ U, ∀ y ∈ U, d l (f.func x) (f.func y) ≤ L * d i x y) →
      matrix d g (f.func '' U) j l / L ≤ matrix d (g*f) U j i) := by
  refine ⟨?_,?_,fun h => compZeroRadius h,fun _ hL h => compLipRadius hL h⟩
  · intro x hx h
    exact hu hx (show g.func (f.func x) = b by rw [h,g.preserves_bot])
  · rintro _ ⟨x,hx,rfl⟩
    exact hu hx

theorem pullbackEndpoints (i j l : I) {L : ENNReal} (hL : positiveFinite L)
    (h : ∀ x ∈ U, ∀ y ∈ U, d l (f.func x) (f.func y) ≤ L * d i x y) :
    (matrix d g (f.func '' U) j l = 0 → matrix d g (f.func '' U) j l / L = 0) ∧
    (matrix d g (f.func '' U) j l = ⊤ → matrix d (g*f) U j i = ⊤) := by
  refine ⟨fun h₀ => by simp [h₀,div_eq_mul_inv],fun ht => ?_⟩
  have H : matrix d g (f.func '' U) j l / L ≤ matrix d (g*f) U j i := compLipRadius hL h
  rw [ht,ENNReal.top_div_of_ne_top hL.2.ne] at H
  exact top_unique H

theorem restrictScaleRadius (σ : Scale X I) (i j : I) (hB : B.Nonempty) (h : B ⊆ A)
    (_ha : A ⊆ dom f) {s : ENNReal} (_hs : positiveFinite s) :
    let a : Region X := ⟨A,hB.mono h⟩
    let b' : Region X := ⟨B,hB⟩
    σ.value i b' ≤ σ.value i a ∧ (σ.value i a < s → σ.value i b' < s) ∧
    (∀ y ∈ B, radius (d i) (d j) f A y ≤ radius (d i) (d j) f B y) ∧
    matrix d f A j i ≤ matrix d f B j i := by
  obtain ⟨h₁,h₂⟩ := scaleRestrict σ i ⟨A,hB.mono h⟩ ⟨B,hB⟩ h s
  exact ⟨h₁,h₂,fun _ _ => restrictRadius h,restrictUniform h⟩

theorem coverConstraint (i j : I) (_hne : A.Nonempty) (_hu : A ⊆ dom f)
    {t : ENNReal} (_ht : positiveFinite t) (hr : t ≤ matrix d f A j i) :
    (∀ x ∈ A, ball (d i) x t ∩ A ⊆ fiber (d j) f A (f.func x)) ∧
    ∀ B ⊆ A, ∀ e, positiveFinite e →
      cover (d j) e (f.func '' B) ≤ cover (d i) t B ∧
      (B.Nonempty → entropy (d j) e (f.func '' B) ≤ entropy (d i) t B) :=
  ⟨fun _ hx => thresholdBall hr hx,fun _ hB _ he =>
    ⟨thresholdCover hB hr he.1,fun _ => thresholdEntropy hB hr he.1⟩⟩

theorem singletonDelta (i j : I) (hne : U.Nonempty) (hu : U ⊆ dom f) {e : ENNReal} (he : positiveFinite e)
    (hg : good (d i) (d j) f U e) :
    ∃ hs, mapDelta d {i} {j} (singleton_nonempty _) (singleton_nonempty _) f U hne hu e he hs =
      delta (d i) (d j) f U e hg := by
  have h (k : I) : subdist d {k} = d k := subfamily_pseudometric_singleton d k
  exact ⟨by simpa only [h] using hg,by simp only [mapDelta,delta,h]⟩

theorem coEntropyBound [Fintype I] (i j : I) (K : I → I → ENNReal) (hK : IsCoLipMatrix d f U K)
    (hk : positiveFinite (K i j)) {e : ENNReal} (he : positiveFinite e) (hU : boundedAtAll (d i) U) :
    (∃ a : ℝ, entropy (d i) e U = a) ∧ (∃ a : ℝ, entropy (d i) (e/K i j) U = a) ∧
    ∃ hg : good (d i) (d j) f U e,
      delta (d i) (d j) f U e hg ≤ entropy (d i) e U - entropy (d i) (e/K i j) U ∧
      (cover (d j) e (f.func '' U) = ⊤ → delta (d i) (d j) f U e hg = ⊥) := by
  obtain ⟨hg,hb⟩ := coDelta d K i j hK hk he hU
  exact ⟨finiteLog hK.1 (hU e he),finiteLog hK.1 (hU _ (divScale he hk)),hg,hb,(deltaBranches hK.1 hg).2.1⟩

theorem radiusSingle (i j : I) (y : X) :
    radius (d i) (subdist d {j}) f U y = radius (d i) (d j) f U y := by
  rw [show subdist d {j} = d j from subfamily_pseudometric_singleton d j]

theorem subfamilyTarget (m : ∀ i, ExtendedPseudoMetric X b (d i)) (J : Set I) (hJ : J.Nonempty)
    (_hu : U ⊆ dom f) {y z : X} (h : subdist d J y z = 0) :
    fiber (subdist d J) f U y = fiber (subdist d J) f U z :=
  fiberTarget (subfamily_pseudometric_is_extended d J hJ m) h

theorem emptyTransform (f g : Op b) : transforms f g ∅ := pointFactor.2 (fun _ h => h.1.elim)

theorem gapDisjoint [Fintype I] (i j : I) (K : I → I → ENNReal)
    (hK : IsCoLipMatrix d f U K) (hk : 0 < K i j) (hr : 0 < matrix d f U j i) :
    Disjoint ({0} : Set ENNReal) (Ici (matrix d f U j i)) ∧
    ∀ x ∈ U, ∀ y ∈ U, d i x y ∈ ({0} : Set ENNReal) ∪ Ici (matrix d f U j i) := by
  exact ⟨Set.disjoint_left.2 (fun _ hz hl => hr.not_ge (Set.mem_singleton_iff.mp hz ▸ hl)),
    fun _ hx _ hy => uniformGap d K i j hK hk hy hr hx⟩

end

namespace Step
theorem pointwiseCoverFails :
    (∀ y ∈ U, 0 < radius usual usual f U y) ∧
    ¬ ∃ t, positiveFinite t ∧ ∀ B ⊆ U, cover usual (1/2) (f.func '' B) ≤ cover usual t B := by
  constructor
  · rintro _ ⟨y,hy,rfl⟩
    exact (pointValue hy).1.symm ▸ (pointValue hy).2
  · rintro ⟨t,ht,h⟩
    obtain ⟨a,_,_,_,hB,hi,ho⟩ := noUniformCover ht
    have H := h _ hB
    rw [hi,ho] at H
    norm_num at H
end Step

namespace Affine
theorem commonFiber (g : Op (none : Line)) (c : ℝ) (h : ∀ x ∈ U, g.func x = pt c)
    (hc : g.func (pt c) ≠ none) :
    U ⊆ dom (g*g) ∧ fiber absolute (g*g) U (g.func (pt c)) = U := by
  obtain ⟨hv,_,hd,_⟩ := sameValue g c h
  refine ⟨hd.2 hc,?_⟩
  ext x
  exact ⟨fun hx => hx.1,fun hx => ⟨hx,by rw [hv _ hx]; exact (readMetric abs).dist_self _⟩⟩
end Affine

namespace Swap
theorem classifications :
    let D := fun _ : Unit => d
    U ⊆ dom (f*f) ∧ activeSet D f U = univ ∧ identSet D f U = ∅ ∧
    activeSet D (f*f) U = ∅ ∧ identSet D (f*f) U = univ := by
  have hd : U ⊆ dom (f*f) := by
    intro x hx
    rcases hx with h|h <;> rw [h] <;> exact Option.some_ne_none _
  obtain ⟨ha,hi,hj,hn⟩ := components
  exact ⟨hd,Set.eq_univ_of_forall (fun _ => ha),Set.eq_empty_iff_forall_notMem.2 (fun _ => hi),
    Set.eq_empty_iff_forall_notMem.2 (fun _ => hn),Set.eq_univ_of_forall (fun _ => hj)⟩
theorem inputAndOutput :
    channels false a c = ⊤ ∧ channels true a c = 1 ∧ U ⊆ dom (1 : Op (none : Option Bool)) := by
  refine ⟨rfl,rfl,?_⟩
  intro x hx
  rcases hx with h|h <;> rw [h] <;> exact Option.some_ne_none _
end Swap

namespace Floor
theorem fourDomains :
    (D (Icc 0 (1/2))).Nonempty ∧ (D (Icc (9/10) (11/10))).Nonempty ∧
    (D {0,2}).Nonempty ∧ (D (Icc 0 2)).Nonempty :=
  ⟨realNonempty (nonempty_Icc.mpr (by norm_num)),realNonempty (nonempty_Icc.mpr (by norm_num)),
    realNonempty ⟨0,Or.inl rfl⟩,realNonempty (nonempty_Icc.mpr (by norm_num))⟩
end Floor

namespace Rearrange
theorem table :
    (f.func (pt 0),f.func (pt 1),f.func (pt 2),f.func (pt 3)) = (pt 0,pt 1,pt 2,pt 3) ∧
    (g.func (pt 0),g.func (pt 1),g.func (pt 2),g.func (pt 3)) = (pt 0,pt 3,pt 1,pt 2) := by
  norm_num [f,g,U,pt]
theorem scales :
    boundedAtAll usual U ∧ ((7/4)/3 : ENNReal) = 7/12 ∧
    cover usual (7/4) (f.func '' U) = cover usual ((7/4)/1) U ∧
    cover usual (7/4) (g.func '' U) < cover usual ((7/4)/3) U := by
  have hfin : U.Finite := carrier ▸ S.finite_toSet
  obtain ⟨_,_,hf,hf',hg,hg'⟩ := numericalBounds
  refine ⟨fun _ he => finiteCover (readMetric id) hfin he.1,?_,hf.trans hf'.symm,?_⟩
  · apply le_antisymm <;> apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).1 <;>
      norm_num [ENNReal.toReal_div]
  · rw [hg,hg']; norm_num
end Rearrange
end
end MG
