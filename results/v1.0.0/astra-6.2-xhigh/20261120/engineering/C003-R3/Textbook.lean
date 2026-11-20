import Chapter

open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
variable {X I : Type} {b : X} {d : I → D X} {U : Set X} {F G : Op b}

theorem row_constraints [Fintype I] (_hU : U ⊆ dom F) {i : I} (h : Const (d i) F.func U)
    (x : X) (hx : x ∈ U) (y : X) (hy : y ∈ U) :
    d i (F.func x) (F.func y) ≤ ∑ k, (0 : ENNReal)*d k x y ∧
    ∑ k, (0 : ENNReal)*d k x y = 0 :=
  ⟨zero_row h hx hy,by simp⟩

theorem composition_sets (hd : ∀ i, ExtendedPseudoMetric X b (d i)) (hU : U ⊆ dom (G*F)) :
    let C := components d (G*F) U hU
    let A := components d F U (comp_domains hU).1
    let B := components d G (F.func '' U) (comp_domains hU).2
    C.2.2 ⊆ A.2.2 ∪ B.2.2 ∧ A.2.1 ∩ B.2.1 ⊆ C.2.1 :=
  ⟨fun i hi => comp_active (f := F.func) (g := G.func) (hd i) hi,
   fun i hi => comp_ident (f := F.func) (g := G.func) (hd i) hi.1 hi.2⟩

theorem chain_sets (hd : ∀ i, ExtendedPseudoMetric X b (d i)) (fs : List (Op b))
    (hU : U ⊆ dom (OperatorChain fs.reverse)) :
    (components d (OperatorChain fs.reverse) U hU).2.2 ⊆
      ⋃ stage ∈ stages fs U, {i | Active (d i) stage.1.func stage.2} := by
  intro i hi
  obtain ⟨s,hs,h⟩ := (stages_spec fs (d i)).mp (chain_active (hd i) fs hi)
  exact mem_iUnion.mpr ⟨s,mem_iUnion.mpr ⟨hs,h⟩⟩

theorem subfamily_fiber_target (hd : ∀ i, ExtendedPseudoMetric X b (d i))
    (_hU : U ⊆ dom F) {J : Set I} (hJ : J.Nonempty) {y z : X}
    (h : subD d J y z = 0) :
    fiber (subD d J) F.func U y = fiber (subD d J) F.func U z :=
  fiber_target (subfamily_pseudometric_is_extended d J hJ hd) h

def pointRadius (p q : D X) (F : Op b) (U : Set X) (_ : U ⊆ dom F) (y : U) :=
  rad p q F.func U y
def uniformRadius (p q : D X) (F : Op b) (A U : Set X) (_ : A.Nonempty)
    (_ : A ⊆ U) (_ : U ⊆ dom F) := uniform p q F.func A U

theorem radius_representations (p q : D X) {A : Set X} (ha : A.Nonempty) (h : A ⊆ U)
    (hU : U ⊆ dom F) :
    uniformRadius p q F A U ha h hU = ⨅ y : A, pointRadius p q F U hU ⟨y,h y.2⟩ := rfl

theorem matrix_composition (_hn : U.Nonempty) (_hU : U ⊆ dom (G*F)) (i j l : I) :
    ((∀ a ∈ F.func '' U, ∀ c ∈ F.func '' U, d l a c = 0 → d j (G.func a) (G.func c) = 0) →
       N d F.func U l i ≤ N d (G*F).func U j i) ∧
    (∀ L, PosFin L → (∀ x ∈ U, ∀ y ∈ U, d l (F.func x) (F.func y) ≤ L*d i x y) →
       N d G.func (F.func '' U) j l / L ≤ N d (G*F).func U j i) :=
  ⟨fun hz => comp_zero (f := F.func) (g := G.func) hz,
   fun _ hl h => comp_lip (f := F.func) (g := G.func) hl h⟩

theorem threshold_sets (S : Scale X I) (A : {A : Set X // A.Nonempty}) (_hA : A.val ⊆ dom F)
    {t u t' u' : ENNReal} (_ht : PosFin t) (_hu : PosFin u) (_ht' : PosFin t') (_hu' : PosFin u')
    (ht : t ≤ t') (hu : u ≤ u') :
    {ij : I × I | (channel S A d F.func t u ij.1 ij.2).1 = true} ⊆
      {ij | (channel S A d F.func t' u ij.1 ij.2).1 = true} ∧
    {ij : I × I | (channel S A d F.func t u' ij.1 ij.2).2 = true} ⊆
      {ij | (channel S A d F.func t u ij.1 ij.2).2 = true} :=
  ⟨fun _ => scale_threshold ht,fun _ => null_threshold hu⟩

theorem separation_witness (_hn : U.Nonempty) (_hU : U ⊆ dom F) (i j : I) {τ : ENNReal}
    (_ht : PosFin τ) (_small : N d F.func U j i < τ) (α : ENNReal) (_hα : PosFin α)
    (h₁ : N d F.func U j i < α) (_h₂ : α < τ) :
    ∃ x ∈ U, ∃ y ∈ U, ∃ ε, PosFin ε ∧ d i x y < α ∧ ε ≤ d j (F.func x) (F.func y) :=
  uniform_witness h₁

theorem cover_constraints (_hn : U.Nonempty) (_hU : U ⊆ dom F) (i j : I) {τ : ENNReal}
    (_ht : PosFin τ) (h : τ ≤ N d F.func U j i) {B : Set X} (hb : B ⊆ U) {ε : ENNReal}
    (he : PosFin ε) :
    (∀ x ∈ U, ball (d i) x τ ∩ U ⊆ fiber (d j) F.func U (F.func x)) ∧
    cov (d j) ε (F.func '' B) ≤ cov (d i) τ B ∧
    (B.Nonempty → ent (d j) ε (F.func '' B) ≤ ent (d i) τ B) :=
  ⟨fun _ hx => threshold_ball h hx,threshold_cover hb h he.1,fun _ => threshold_entropy hb h he.1⟩

theorem small_image (_hU : U ⊆ dom F) (hn : U.Nonempty) (i j : I) {t u : ENNReal}
    (_ht : PosFin t) (_hu : PosFin u) (h : diameter (d i) U < t) (hh : t ≤ u) :
    (u ≤ N d F.func U j i ↔ Const (d j) F.func U) ∧
    (u ≤ N d F.func U j i → ∀ e, PosFin e → cov (d j) e (F.func '' U) = 1) :=
  ⟨small_iff h hh,fun hr _ he => small_cover hn h hh hr he.1⟩

theorem distance_gap [Fintype I] {K : I → I → ENNReal} (hK : IsCoLipMatrix d F U K)
    {i j : I} (h : 0 < K i j) (hr : 0 < N d F.func U j i) :
    Disjoint ({0} : Set ENNReal) (Ici (N d F.func U j i)) ∧
    ∀ x ∈ U, ∀ y ∈ U, d i x y ∈ ({0} : Set ENNReal) ∪ Ici (N d F.func U j i) :=
  ⟨by simp [hr.not_ge],fun _ hx _ hy => uniform_gap hK h hx hy⟩

/-- Inclusion of full zero-distance relations is exactly refinement of the partitions on U. -/
theorem finer_iff_blocks [Nonempty I] (hd : ∀ i, ExtendedPseudoMetric X b (d i))
    (_hF : U ⊆ dom F) (_hG : U ⊆ dom G) :
    finer d U F.func G.func ↔
      ∀ S ∈ blocks (subD d univ) F.func U,
        ∃ T ∈ blocks (subD d univ) G.func U, S ⊆ T := by
  let p := subD d univ
  have hp : ExtendedPseudoMetric X b p :=
    subfamily_pseudometric_is_extended d univ univ_nonempty hd
  constructor
  · rintro h _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨fiber p G.func U (G.func x), ⟨_, ⟨x, hx, rfl⟩, rfl⟩, ?_⟩
    intro y hy
    let u : U := ⟨x, hx⟩
    let v : U := ⟨y, hy.1⟩
    exact (zeroRel_fiber hd u v).mp (h ((zeroRel_fiber hd u v).mpr hy))
  · intro h
    rintro ⟨x, y⟩ hxy
    let S := fiber p F.func U (F.func x)
    have hs : S ∈ blocks p F.func U := ⟨_, (img U F.func x).2, rfl⟩
    obtain ⟨_, ⟨z, _, rfl⟩, hST⟩ := h S hs
    have hx := hST (show x.val ∈ S from ⟨x.2, hp.dist_self _⟩)
    have hy := hST ((zeroRel_fiber hd x y).mp hxy)
    apply (zeroRel_fiber hd x y).mpr
    exact ⟨y.2, (zero_right hp hx.2).trans hy.2⟩

theorem legal_iff_le_pointRadius {p q : D X} {r : ENNReal} (hU : U ⊆ dom F) (y : U) :
    r ∈ legal p q F.func U y ↔ PosFin r ∧ r ≤ pointRadius p q F U hU y :=
  ⟨fun h => ⟨h.1, le_sSup h⟩, fun h => ⟨h.1, fun x hx hxy => by
    obtain ⟨ρ, hρ, hlt⟩ := rad_notation.mp (hxy.trans_le h.2)
    exact hρ.2 x hx hlt⟩⟩

theorem pointRadius_top_iff {p q : D X} (hU : U ⊆ dom F) (y : U) :
    pointRadius p q F U hU y = ⊤ ↔
      ∀ r, PosFin r → r ∈ legal p q F.func U y := by
  constructor
  · intro ht r hr
    exact (legal_iff_le_pointRadius hU y).mpr ⟨hr, ht ▸ le_top⟩
  · intro h
    apply top_unique
    by_contra! hlt
    obtain ⟨r, hr, hfin⟩ := exists_between hlt
    exact hr.not_ge (le_sSup (h r ⟨(zero_le _).trans_lt hr, hfin⟩))

theorem swap_domains : Swap.U.Nonempty ∧ Swap.U ⊆ dom (Swap.F * Swap.F) ∧
    Swap.U ⊆ dom (run (id : Bool → Bool)) := by
  refine ⟨⟨some false, some_area.mpr trivial⟩, ?_, area_dom _ _⟩
  intro x hx
  have h : Swap.F.func x ∈ Swap.U := Swap.image_dom.2 ▸ mem_image_of_mem _ hx
  exact Swap.image_dom.1 h

/-- In a one-component gauge, the restricted Lip certificate is the scalar bound. -/
theorem singleton_lip_iff [Fintype I] [Subsingleton I] (i : I) (L : I → I → ENNReal) :
    IsLipMatrix d F U L ↔ HasScalarLipBound d F U i i (L i i) := by
  constructor
  · intro h
    exact ⟨h.1, single_component_lip_matrix_ineq d F U L i h⟩
  · rintro ⟨hU, h⟩
    refine ⟨hU, ?_⟩
    intro x hx y hy j
    rw [Subsingleton.elim j i, Fintype.sum_subsingleton _ i]
    exact h x hx y hy

/-- The lower certificate additionally requires a nonempty evaluation domain. -/
theorem singleton_colip_iff [Fintype I] [Subsingleton I] (i : I) (K : I → I → ENNReal) :
    IsCoLipMatrix d F U K ↔ U.Nonempty ∧ U ⊆ dom F ∧
      ∀ x ∈ U, ∀ y ∈ U, K i i * d i x y ≤ d i (F.func x) (F.func y) := by
  constructor
  · rintro ⟨hn, hU, h⟩
    refine ⟨hn, hU, ?_⟩
    intro x hx y hy
    simpa only [Fintype.sum_subsingleton _ i] using h x hx y hy i
  · rintro ⟨hn, hU, h⟩
    refine ⟨hn, hU, ?_⟩
    intro x hx y hy j
    rw [Subsingleton.elim j i, Fintype.sum_subsingleton _ i]
    exact h x hx y hy

/-- Reading a singleton-channel certificate in the frozen matrix representation. -/
theorem factor_lip_of_matrices [Fintype I] [Subsingleton I] (i : I)
    {K L : I → I → ENNReal}
    (hK : IsCoLipMatrix d F U K) (hL : IsLipMatrix d G U L)
    (hk : PosFin (K i i)) (hl : L i i < ⊤) (T : F.func '' U → X)
    (ht : ∀ x : U, T (img U F.func x) = G.func x) (u v : F.func '' U) :
    d i (T u) (T v) ≤ (L i i / K i i) * d i u v := by
  exact factor_lip hk hl T ht ((singleton_colip_iff i K).mp hK).2.2
    ((singleton_lip_iff i L).mp hL).2 u v

/-- Each point of the two-point domain is its entire finite input ball there. -/
theorem infinite_input_balls (y : Swap.U) {r : ENNReal} (hr : PosFin r) :
    ball (InfiniteInput.d false) (y : Option Bool) r ∩ Swap.U = {y.val} := by
  rcases y with ⟨_, a, _, rfl⟩
  ext z
  constructor
  · rintro ⟨hz, c, _, rfl⟩
    change InfiniteInput.d false (some c) (some a) < r at hz
    by_contra hn
    have hca : c ≠ a := fun h => hn (by simp [h])
    simp [InfiniteInput.d, liftDist, discrete, hca] at hz
  · rintro rfl
    refine ⟨?_, some_area.mpr trivial⟩
    change InfiniteInput.d false (some a) (some a) < r
    rw [(InfiniteInput.model false).dist_self]
    exact hr.1

theorem infinite_input_radius (j : Bool) (y : Swap.U) :
    rad (InfiniteInput.d false) (InfiniteInput.d j) (run id).func Swap.U y = ⊤ := by
  apply top_unique
  calc
    ⊤ = N InfiniteInput.d (run id).func Swap.U j false := (InfiniteInput.both j).1.symm
    _ ≤ _ := iInf_le _ y

/-- In the finite, nonempty case the two infima give actual least elements. -/
theorem subfamily_minima [Finite I] {J : Set I} (hj : J.Nonempty) (i : I)
    (hn : U.Nonempty) (hU : U ⊆ dom F) (y : U) :
    IsLeast (Set.range (fun j : J => pointRadius (d i) (d j) F U hU y))
      (pointRadius (d i) (subD d J) F U hU y) ∧
    IsLeast (Set.range (fun j : J => N d F.func U j i))
      (uniformRadius (d i) (subD d J) F U U hn Subset.rfl hU) := by
  have least (v : J → ENNReal) : IsLeast (Set.range v) (⨅ j, v j) :=
    ⟨attained_min hj v, fun _ ⟨j, hj'⟩ => hj' ▸ iInf_le v j⟩
  constructor
  · unfold pointRadius
    rw [rad_sub]
    exact least _
  · unfold uniformRadius
    rw [uniform_sub]
    exact least _

theorem fiber_cut_on_domain (hd : ∀ k, ExtendedPseudoMetric X b (d k))
    (hU : U ⊆ dom F) (i j : I) (y z : U)
    (h : z.val ∈ fiber (d j) F.func U (F.func y) ∨
      d i y z < pointRadius (d i) (d j) F U hU y) :
    d j (F.func y) (F.func z) = 0 :=
  cut_alternatives (hd i) (hd j) z.2 h

theorem restrict_radii {A B : Set X} (hn : B.Nonempty) (h : B ⊆ A) (ha : A ⊆ dom F)
    (p q : D X) :
    (∀ y : B, pointRadius p q F A ha ⟨y, h y.2⟩ ≤ pointRadius p q F B (h.trans ha) y) ∧
    uniformRadius p q F A A (hn.mono h) Subset.rfl ha ≤
      uniformRadius p q F B B hn Subset.rfl (h.trans ha) :=
  ⟨fun _ => rad_restrict h, uniform_restrict h⟩

theorem log_strictMono : StrictMono log2_ereal := by
  intro a c h
  have h₁ : a ≠ ⊤ := h.ne_top
  have h₂ : c ≠ 0 := (zero_le _ |>.trans_lt h).ne'
  by_cases ha : a = 0
  · by_cases hc : c = ⊤ <;> simp [log2_ereal, ha, hc, h₂]
  by_cases hc : c = ⊤
  · simp [log2_ereal, ha, h₁, hc]
  simp only [log2_ereal, if_neg ha, if_neg hc, if_neg h₁, if_neg h₂]
  exact EReal.coe_lt_coe_iff.mpr
    (Real.logb_lt_logb one_lt_two (ENNReal.toReal_pos ha h₁) ((ENNReal.toReal_lt_toReal h₁ hc).mpr h))

theorem cover_entropy_iff {p q : D X} {B : Set X} {e r : ENNReal} :
    cov q e (F.func '' B) ≤ cov p r B ↔ ent q e (F.func '' B) ≤ ent p r B :=
  log_strictMono.le_iff_le.symm

theorem step_no_uniform_cover :
    (∀ y ∈ area punct, 0 < rad (line id) (line id) (run step).func (area punct) y) ∧
    ¬ ∃ τ, PosFin τ ∧ ∀ B ⊆ area punct,
      cov (line id) (1/2) ((run step).func '' B) ≤ cov (line id) τ B := by
  constructor
  · rintro _ ⟨y, hy, rfl⟩
    exact (step_radius hy).1.symm ▸ (step_radius hy).2
  · rintro ⟨τ, ht, h⟩
    obtain ⟨a, _, _, _, hB, hin, hout⟩ := step_two ht
    have hc := h {pt (-a), pt a} hB
    rw [hout, hin] at hc
    norm_num at hc

theorem small_domain_type (i j : I) (hn : U.Nonempty) (hU : U ⊆ dom F)
    {t u : ENNReal} (ht : PosFin t) (hu : PosFin u) (hdiam : diameter (d i) U < t)
    (htu : t ≤ u) :
    let kind := channel (diamScale d) ⟨U, hn⟩ d F.func t u i j
    kind.1 = true ∧ (kind.2 = true ↔ Const (d j) F.func U) := by
  obtain ⟨h₁, h₂⟩ := threshold_spec (S := diamScale d) ⟨U, hn⟩ hU ht hu i j
  exact ⟨h₁.mpr hdiam, h₂.trans (small_iff hdiam htu)⟩

theorem finite_mapping_entropy (hd : ∀ i, ExtendedPseudoMetric X b (d i))
    (hn : U.Nonempty) (hf : U.Finite) (hU : U ⊆ dom F) {J K : Set I}
    (hj : J.Nonempty) (hk : K.Nonempty) {e : ENNReal} (he : PosFin e) :
    ∃ hw, ∃ t : ℝ, mappingEntropy d F U hn hU J K hj hk e he hw = t := by
  obtain ⟨hin, hout, _, _, hw⟩ := finite_ends hd J K hj hk hn hf F.func he
  exact ⟨hw, (delta_cases hn hw).2.2 hin.2 hout.2⟩

theorem singleton_mapping (i j : I) (hn : U.Nonempty) (hU : U ⊆ dom F)
    {e : ENNReal} (he : PosFin e) (hw : Defined (d i) (d j) F.func U e) :
    mappingEntropy d F U hn hU {i} {j} (singleton_nonempty _) (singleton_nonempty _)
      e he ((singleton_channel i j e).mpr hw) = delta (d i) (d j) F.func U e hw :=
  singleton_delta i j e _

theorem lip_mapping_bound (i j : I) (hn : U.Nonempty) {e L : ENNReal} (he : PosFin e)
    (hL : PosFin L) (h : HasScalarLipBound d F U i j L) (ht : TB (d i) U) :
    ∃ hw, (∃ s : ℝ, ent (d i) e U = s) ∧ (∃ t : ℝ, ent (d i) (e/L) U = t) ∧
      (∃ v : ℝ, ent (d j) e (F.func '' U) = v) ∧
      ent (d i) e U - ent (d i) (e/L) U ≤
        mappingEntropy d F U hn h.1 {i} {j} (singleton_nonempty _) (singleton_nonempty _) e he hw := by
  obtain ⟨hs, hv, hw, hb⟩ := lip_delta hn ht he hL h.2
  exact ⟨(singleton_channel i j e).mpr hw, hs, finite_entropy hn (ht _ (div_pf he hL)), hv,
    (singleton_mapping i j hn h.1 he hw).symm ▸ hb⟩

theorem colip_mapping_bound [Fintype I] {i j : I} {K : I → I → ENNReal}
    (h : IsCoLipMatrix d F U K) (hk : PosFin (K i j)) (ht : TB (d i) U)
    {e : ENNReal} (he : PosFin e) :
    ∃ hw, let Δ := mappingEntropy d F U h.1 h.2.1 {i} {j}
                         (singleton_nonempty _) (singleton_nonempty _) e he hw
          (∃ s : ℝ, ent (d i) e U = s) ∧ (∃ t : ℝ, ent (d i) (e / K i j) U = t) ∧
          Δ ≤ ent (d i) e U - ent (d i) (e / K i j) U ∧
          (cov (d j) e (F.func '' U) = ⊤ → Δ = ⊥) := by
  obtain ⟨hw, hb⟩ := colip_delta h hk ht he
  refine ⟨(singleton_channel i j e).mpr hw, ?_⟩
  dsimp only
  rw [singleton_mapping i j h.1 h.2.1 he hw]
  exact ⟨finite_entropy h.1 (ht e he), finite_entropy h.1 (ht _ (div_pf he hk)), hb,
    (delta_cases h.1 hw).2.1⟩

theorem translation_domains : fourMag.Nonempty ∧
    fourMag ⊆ dom (operator_identity : Op (none : Option ℝ)) ∩ dom transF := by
  refine ⟨⟨pt 0, by simp [fourMag]⟩, ?_⟩
  intro x hx
  refine ⟨?_, translate_blocks.2.1 hx⟩
  rcases (show x = pt (-3) ∨ x = pt (-2) ∨ x = pt 0 ∨ x = pt 2 from hx) with
    rfl | rfl | rfl | rfl <;> exact Option.some_ne_none _

theorem floor_domains {S : Set ℝ}
    (hs : S ∈ ({Icc 0 (1/2), Icc (9/10) (11/10), {0,2}, Icc 0 2} : Set (Set ℝ))) :
    S.Nonempty ∧ (area S).Nonempty ∧ area S ⊆ dom (run floorF) := by
  have hn : S.Nonempty := by
    rcases (show S = Icc 0 (1/2) ∨ S = Icc (9/10) (11/10) ∨ S = {0,2} ∨ S = Icc 0 2
      from hs) with rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨0, by simp⟩
    · exact ⟨0, by norm_num⟩
  exact ⟨hn, hn.image some, area_dom _ _⟩

/-- At a finite point radius, the distance on the boundary can separate the outputs. -/
theorem radius_boundary :
    let U := area ({0, 2} : Set ℝ)
    pt 0 ∈ U ∧ pt 2 ∈ U ∧ U ⊆ dom (run floorF) ∧
    rad (line id) (line id) (run floorF).func U (pt 0) = 2 ∧
    line id (pt 2) (pt 0) = 2 ∧
    line id ((run floorF).func (pt 2)) ((run floorF).func (pt 0)) = 2 := by
  dsimp only
  have h₀ : pt 0 ∈ area ({0, 2} : Set ℝ) := some_area.mpr (by simp)
  have h₂ : pt 2 ∈ area ({0, 2} : Set ℝ) := some_area.mpr (by simp)
  have hpair := congrArg Prod.snd floor_pair.1
  change uniform (line id) (line id) (run floorF).func _ _ = 2 at hpair
  have hin : line id (pt 2) (pt 0) = 2 := by norm_num [pt]
  have hout : line id ((run floorF).func (pt 2)) ((run floorF).func (pt 0)) = 2 := by
    norm_num [pt, floorF]
  refine ⟨h₀, h₂, area_dom _ _, le_antisymm ?_ ?_, hin, hout⟩
  · apply le_of_not_gt
    intro h
    have hz := below_rad h₂ (hin.symm ▸ h)
    rw [hout] at hz
    norm_num at hz
  · rw [← hpair]
    exact iInf_le _ (⟨pt 0, h₀⟩ : area ({0, 2} : Set ℝ))

end
end C3
