import Chapter.Radius
import Chapter.Cover

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {f g : Operator X bot} {U A : Set X} {J K : Set I}
variable {i j : I} {x y : X} {P Q : X → X → ℝ≥0∞}

theorem component_membership (_hU : U ⊆ dom f) :
    (i ∈ Const d f U ↔ ∀ a ∈ U, ∀ b ∈ U, d i (f.func a) (f.func b) = 0) ∧
    (i ∈ Ident d f U ↔
      (¬ ∀ a ∈ U, ∀ b ∈ U, d i (f.func a) (f.func b) = 0) ∧
      ∀ a ∈ U, d i (f.func a) a = 0) ∧
    (i ∈ Active d f U ↔ i ∉ Const d f U ∧ i ∉ Ident d f U) :=
  ⟨Iff.rfl, Iff.rfl, not_or⟩

theorem fiber_membership (_hU : U ⊆ dom f) (_hJ : J.Nonempty) :
    x ∈ fiber (subfamily_pseudometric d J) f U y ↔
      x ∈ U ∧ ∀ j ∈ J, d j (f.func x) y = 0 := by
  simp [fiber, subfamily_zero]

theorem fiber_missing (_hU : U ⊆ dom f) (_hJ : J.Nonempty)
    (h : ∀ z ∈ f.func '' U, 0 < subfamily_pseudometric d J z y) :
    fiber (subfamily_pseudometric d J) f U y = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x hx => (h _ ⟨x,hx.1,rfl⟩).ne' hx.2

theorem finer_iff_blocks (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom f ∩ dom g) :
    FiberFiner d U f g ↔
      ∀ B ∈ fiberBlocks (subfamily_pseudometric d Set.univ) f U,
        ∃ C ∈ fiberBlocks (subfamily_pseudometric d Set.univ) g U, B ⊆ C := by
  constructor
  · rintro h _ ⟨_,⟨x,hx,rfl⟩,rfl⟩
    refine ⟨_,⟨g.func x,⟨x,hx,rfl⟩,rfl⟩,fun y hy => ?_⟩
    exact (zeroPairs_fiber hd (f := g) hx hy.1).mp
      (h ((zeroPairs_fiber hd hx hy.1).mpr hy))
  · rintro h ⟨x,y⟩ hp
    have hx : x ∈ U := hp.1
    have hy : y ∈ U := hp.2.1
    obtain ⟨_,⟨z,hz,rfl⟩,hsub⟩ := h _ ⟨f.func x,⟨x,hx,rfl⟩,rfl⟩
    have hx0 : x ∈ fiber (subfamily_pseudometric d Set.univ) g U z :=
      hsub ((zeroPairs_fiber hd hx hx).mp ⟨hx,hx,fun i => (hd i).dist_self _⟩)
    have hy0 : y ∈ fiber (subfamily_pseudometric d Set.univ) g U z :=
      hsub ((zeroPairs_fiber hd hx hy).mp hp)
    refine ⟨hx,hy,fun j => ?_⟩
    have ha := (subfamily_zero d Set.univ _ _).mp hx0.2 j (Set.mem_univ _)
    have hb := (subfamily_zero d Set.univ _ _).mp hy0.2 j (Set.mem_univ _)
    exact (zero_left (hd j) ha _).trans (((hd j).symm _ _).trans hb)

theorem finer_iff_quotient (hd : ∀ i, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom f ∩ dom g) : FiberFiner d U f g ↔ QuotFactor hd f g U :=
  (quot_factor hd hU).symm

theorem radius_ball_formula (_hU : U ⊆ dom f) (_hy : y ∈ U) :
    radius f P Q U y =
      sSup {r | 0 < r ∧ r < ⊤ ∧ ball P y r ∩ U ⊆ {x ∈ U | Q (f.func x) (f.func y) = 0}} := by
  unfold radius
  congr 1
  ext r
  exact and_assoc

theorem radius_singleton (_hU : U ⊆ dom f) (_hy : y ∈ U) :
    radius f (d i) (subfamily_pseudometric d {j}) U y = radius f (d i) (d j) U y := by
  rw [subfamily_pseudometric_singleton]

theorem uniform_ball_formula (_hn : A.Nonempty) (_hAU : A ⊆ U) (_hU : U ⊆ dom f) :
    uniform f P Q A U = ⨅ y ∈ A, radius f P Q U y := by
  unfold uniform
  apply le_antisymm
  · exact le_iInf fun y => le_iInf fun hy => uniform_le_point (f := f) (P := P) (Q := Q) (U := U) hy
  · exact le_iInf fun y : A => iInf_le_of_le (y : X) (iInf_le_of_le y.2 le_rfl)

theorem nullMatrix_formula (hn : U.Nonempty) (hU : U ⊆ dom f) :
    nullMatrix d f U j i = ⨅ y ∈ U, radius f (d i) (d j) U y :=
  uniform_ball_formula hn Set.Subset.rfl hU

theorem radius_minimum [Finite I] (hJ : J.Nonempty) (hU : U ⊆ dom f) (hy : y ∈ U) :
    ∃ j ∈ J, radius f P (subfamily_pseudometric d J) U y = radius f P (d j) U y ∧
      ∀ k ∈ J, radius f P (d j) U y ≤ radius f P (d k) U y := by
  rw [radius_subfamily hJ hU hy]
  obtain ⟨j,hj⟩ := iInf_attains hJ (fun j => radius f P (d j) U y)
  exact ⟨j,j.2,hj,fun k hk => hj ▸ iInf_le (fun l : J => radius f P (d l) U y) ⟨k,hk⟩⟩

theorem uniform_minimum [Finite I] (hJ : J.Nonempty) (_hn : U.Nonempty) (hU : U ⊆ dom f) :
    ∃ j ∈ J, uniform f (d i) (subfamily_pseudometric d J) U U = nullMatrix d f U j i ∧
      ∀ k ∈ J, nullMatrix d f U j i ≤ nullMatrix d f U k i := by
  rw [uniform_subfamily hJ hU]
  obtain ⟨j,hj⟩ := iInf_attains hJ (fun j => nullMatrix d f U j i)
  exact ⟨j,j.2,hj,fun k hk => hj ▸ iInf_le (fun l : J => nullMatrix d f U l i) ⟨k,hk⟩⟩

theorem threshold_exclusive (σ : ScaleFamily X I) (hn : A.Nonempty) (s t : ℝ≥0∞) :
    ∃! q : Bool × Bool, q = thresholdType σ d f A hn s t i j :=
  ⟨_,rfl,fun _ h => h⟩

theorem small_threshold_type (hA : A ⊆ dom f) (hn : A.Nonempty) {s t : ℝ≥0∞}
    (hs : FinitePositive s) (ht : FinitePositive t)
    (hd : diameter (d i) A < s) (hst : s ≤ t) :
    (thresholdType (diameterScale d) d f A hn s t i j).1 = true ∧
    ((thresholdType (diameterScale d) d f A hn s t i j).2 = true ↔
      ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0) := by
  simp only [thresholdType, diameterScale, decide_eq_true_eq]
  exact ⟨hd,small_iff hA hn hs ht hd hst⟩

theorem subfamily_cover_singleton (r : ℝ≥0∞) :
    covering_number (subfamily_pseudometric d {i}) r U = covering_number (d i) r U ∧
    subfamily_metric_entropy d {i} r U = metric_entropy (d i) r U := by
  constructor
  · rw [subfamily_pseudometric_singleton]
  · exact subfamily_metric_entropy_singleton d i r U

def SubfamilyGapDefined (d : I → X → X → ℝ≥0∞) (f : Operator X bot)
    (U : Set X) (J K : Set I) (r : ℝ≥0∞) : Prop :=
  GapDefined f (subfamily_pseudometric d J) (subfamily_pseudometric d K) U r

noncomputable def subfamilyGap (d : I → X → X → ℝ≥0∞) (f : Operator X bot)
    (U : Set X) (J K : Set I) (r : ℝ≥0∞)
    (_hU : U ⊆ dom f) (_hne : U.Nonempty) (_hJ : J.Nonempty) (_hK : K.Nonempty)
    (_hr : FinitePositive r) (h : SubfamilyGapDefined d f U J K r) : EReal :=
  entropyGap f (subfamily_pseudometric d J) (subfamily_pseudometric d K) U r h

theorem subfamily_gap_formula {r : ℝ≥0∞} (hU : U ⊆ dom f) (hne : U.Nonempty)
    (hJ : J.Nonempty) (hK : K.Nonempty) (hr : FinitePositive r)
    (h : SubfamilyGapDefined d f U J K r) :
    subfamilyGap d f U J K r hU hne hJ hK hr h =
      subfamily_metric_entropy d J r U - subfamily_metric_entropy d K r (f.func '' U) := rfl

theorem gap_excludes_double_infinity {r : ℝ≥0∞} :
    ¬ SubfamilyGapDefined d f U J K r ↔
      covering_number (subfamily_pseudometric d J) r U = ⊤ ∧
        covering_number (subfamily_pseudometric d K) r (f.func '' U) = ⊤ := by
  simp [SubfamilyGapDefined, GapDefined, not_or, not_lt]


theorem threshold_domain_radius {B : Set X}
    (_hB : B.Nonempty) (hBA : B ⊆ A) (_hA : A ⊆ dom f) (hy : y ∈ B) :
    radius f P Q A y ≤ radius f P Q B y := radius_restrict hBA hy

theorem finite_cover_minimum {r : ℝ≥0∞} (_hr : FinitePositive r)
    (h : covering_number P r U < ⊤) :
    ∃ S : Finset X, (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ S, ball P c r ∧
      covering_number P r U = S.card ∧
      ∀ T : Finset X, (↑T : Set X) ⊆ U → U ⊆ ⋃ c ∈ T, ball P c r → S.card ≤ T.card := by
  classical
  have hnet : ∃ S, InternalEpsilonNet P r U S := by
    by_contra hn
    exact h.ne ((covering_number_eq_top_iff _ _ _).mpr hn)
  obtain ⟨S,hS,he,hm⟩ := covering_number_attained _ _ _ hnet
  have hs := net_iff_ball_cover.mp hS
  exact ⟨S,hs.1,hs.2,he,fun T ht ht' => hm T (net_iff_ball_cover.mpr ⟨ht,ht'⟩)⟩

theorem finite_gap_conditions {r : ℝ≥0∞} (_hr : FinitePositive r) :
    covering_number P r U = ⊤ ↔
      ¬ ∃ S : Finset X, (↑S : Set X) ⊆ U ∧ U ⊆ ⋃ c ∈ S, ball P c r := by
  rw [covering_number_eq_top_iff]
  simp only [net_iff_ball_cover]


theorem chain_domain_valid (fs : List (Operator X bot)) (U : Set X) :
    U ⊆ dom (chain fs) →
      match fs with
      | [] => U ⊆ dom (1 : Operator X bot)
      | f :: tail => U ⊆ dom f ∧ f.func '' U ⊆ dom (chain tail) := by
  cases fs with
  | nil => exact id
  | cons f tail => exact stage_domains

theorem uniform_gap_disjoint (hr : 0 < nullMatrix d f U j i) :
    Disjoint ({0} : Set ℝ≥0∞) (Set.Ici (nullMatrix d f U j i)) := by
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  have he : x = 0 := hx
  exact hr.not_ge (he ▸ hx')

end Chapter
