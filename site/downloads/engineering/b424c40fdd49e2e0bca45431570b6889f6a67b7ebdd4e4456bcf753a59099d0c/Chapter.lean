import Rearrangement
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

variable {d : I → D X} {F G : Op b} {U : Set X}

def components (d : I → D X) (F : Op b) (U : Set X) (_ : U ⊆ dom F) :
    Set I × Set I × Set I :=
  ({i | Const (d i) F.func U},{i | Ident (d i) F.func U},{i | Active (d i) F.func U})

theorem component_sets (h : U ⊆ dom F) :
    (components d F U h).2.1 = {i | i ∉ (components d F U h).1 ∧
      ∀ x ∈ U, d i (F.func x) x = 0} ∧
    (components d F U h).2.2 = ((components d F U h).1 ∪ (components d F U h).2.1)ᶜ := by
  exact ⟨rfl,by ext i; exact not_or.symm⟩

theorem comp_domains (h : U ⊆ dom (G * F)) : U ⊆ dom F ∧ F.func '' U ⊆ dom G := by
  constructor
  · intro x hx hh
    apply h hx
    change G.func (F.func x) = b
    rw [hh,G.preserves_bot]
  · rintro _ ⟨x,hx,rfl⟩
    exact h hx

def stages : List (Op b) → Set X → List (Op b × Set X)
  | [], _ => []
  | F :: fs, A => (F,A) :: stages fs (F.func '' A)

theorem stages_spec (fs : List (Op b)) (p : D X) : stepActive p fs U ↔
    ∃ stage ∈ stages fs U, Active p stage.1.func stage.2 := by
  induction fs generalizing U with
  | nil => simp [stepActive,stages]
  | cons F tail ih => simp [stages, stepActive, ih]

theorem valid_stages (fs : List (Op b)) (hu : U ⊆ dom (OperatorChain fs.reverse)) :
    ∀ s ∈ stages fs U, s.2 ⊆ dom s.1 := by
  induction fs generalizing U with
  | nil => simp [stages]
  | cons F fs ih =>
    rw [List.reverse_cons, operator_chain_eq_prod, List.prod_append, List.prod_singleton,
      ← operator_chain_eq_prod] at hu
    obtain ⟨h₁,h₂⟩ := comp_domains hu
    simpa [stages] using And.intro h₁ (ih h₂)

theorem fiber_spec (J : Set I) (y x : X) : x ∈ fiber (subD d J) F.func U y ↔
    x ∈ U ∧ ∀ j ∈ J, d j (F.func x) y = 0 := and_congr_right fun _ => sub_zero

theorem finite_max [Finite I] {J : Set I} (hj : J.Nonempty) (x y : X) :
    ∃ j ∈ J, subD d J x y = d j x y ∧ ∀ k ∈ J, d k x y ≤ d j x y := by
  letI : Nonempty J := hj.to_subtype
  obtain ⟨j,h⟩ := exists_eq_ciSup_of_finite (f := fun j : J => d j.val x y)
  exact ⟨j,j.2,h.symm,fun k hk => h ▸ le_iSup (fun j : J => d j.val x y) (⟨k,hk⟩ : J)⟩

theorem fiber_absent (p : D X) {z : X} (h : ∀ y ∈ F.func '' U, 0 < p y z) :
    fiber p F.func U z = ∅ :=
  Set.eq_empty_iff_forall_notMem.mpr fun x hx => (h _ ⟨x,hx.1,rfl⟩).ne' hx.2

theorem relations_on (x y : X) :
    (∃ u v : U, u.val = x ∧ v.val = y ∧ (u,v) ∈ eqRel U F.func) ↔
      x ∈ U ∧ y ∈ U ∧ F.func x = F.func y := by
  constructor
  · rintro ⟨u,v,rfl,rfl,h⟩; exact ⟨u.2,v.2,h⟩
  · rintro ⟨hx,hy,h⟩; exact ⟨⟨x,hx⟩,⟨y,hy⟩,rfl,rfl,h⟩

theorem zero_relations_on (x y : X) :
    (∃ u v : U, u.val = x ∧ v.val = y ∧ (u,v) ∈ zeroRel d U F.func) ↔
      x ∈ U ∧ y ∈ U ∧ GaugeZeroRelated d (F.func x) (F.func y) := by
  constructor
  · rintro ⟨u,v,rfl,rfl,h⟩; exact ⟨u.2,v.2,h⟩
  · rintro ⟨hx,hy,h⟩; exact ⟨⟨x,hx⟩,⟨y,hy⟩,rfl,rfl,h⟩

theorem rad_empty {p q : D X} {y : X} (h : legal p q F.func U y = ∅) :
    rad p q F.func U y = 0 := by simp [rad,h]

theorem matrix_spec {i j : I} :
    N d F.func U j i = ⨅ y : U, rad (d i) (d j) F.func U y := rfl

theorem radius_notation (i j : I) :
    rad (d i) (subD d {j}) F.func U = rad (d i) (d j) F.func U ∧
    uniform (d i) (subD d {j}) F.func U U = N d F.func U j i := by
  simp only [subD,subfamily_pseudometric_singleton,N,and_self]

theorem area_legal {p q : D X} {f : X → X} {S : Set X} {y : X} :
    legal (liftDist p) (liftDist q) (run f).func (area S) (some y) = legal p q f S y := by
  ext r
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro _
  constructor
  · intro h x hx
    exact h (some x) (some_area.mpr hx)
  · rintro h _ ⟨x,hx,rfl⟩
    exact h x hx

theorem four_types (a n t u : ENNReal) : ∃! v : Bool × Bool,
    (v.1 = true ↔ a < t) ∧ (v.2 = true ↔ u ≤ n) := by
  refine ⟨bits a n t u,by simp [bits],?_⟩
  rintro ⟨v,w⟩ hw
  cases v <;> cases w <;> simp_all [bits]

def mappingEntropy (d : I → D X) (F : Op b) (U : Set X) (_ : U.Nonempty) (_ : U ⊆ dom F)
    (J K : Set I) (_ : J.Nonempty) (_ : K.Nonempty) (e : ENNReal) (_ : PosFin e)
    (hw : Defined (subD d J) (subD d K) F.func U e) :=
  delta (subD d J) (subD d K) F.func U e hw

theorem mapping_spec (hu : U.Nonempty) (hdom : U ⊆ dom F) {J K : Set I} (hj : J.Nonempty)
    (hk : K.Nonempty) {e : ENNReal} (he : PosFin e) (hw) :
    mappingEntropy d F U hu hdom J K hj hk e he hw =
    subfamily_metric_entropy d J e U - subfamily_metric_entropy d K e (F.func '' U) := rfl

theorem coverage_meaning (p : D X) (e : ENNReal) (A : Set X) :
    ((∃ S, InternalEpsilonNet p e A S) → ∃ S, InternalEpsilonNet p e A S ∧
      cov p e A = S.card ∧ ∀ T, InternalEpsilonNet p e A T → S.card ≤ T.card) ∧
    (cov p e A = ⊤ ↔ ¬ ∃ S, InternalEpsilonNet p e A S) ∧
    cov p e ∅ = 0 ∧ ent p e A = log2_ereal (cov p e A) :=
  ⟨covering_number_attained p e A,covering_number_eq_top_iff p e A,covering_number_empty p e,rfl⟩

theorem delta_signs {p q : D X} {e : ENNReal} (hu : U.Nonempty) (hw : Defined p q F.func U e) :
    let a := ent p e U
    let b := ent q e (F.func '' U)
    (0 < delta p q F.func U e hw ↔ b < a) ∧
    (delta p q F.func U e hw < 0 ↔ a < b) ∧
    (delta p q F.func U e hw = 0 ↔ a = b) := by
  dsimp only
  have ht : ent p e U ≠ ⊤ ∨ ent q e (F.func '' U) ≠ ⊤ := by
    rcases hw with h | h
    · obtain ⟨a,ha⟩ := finite_entropy hu h; simp [ha]
    · obtain ⟨a,ha⟩ := finite_entropy (hu.image _) h; simp [ha]
  have hb : ent p e U ≠ ⊥ :=
    ((show (⊥ : EReal) < 0 from EReal.bot_lt_zero).trans_le (metric_entropy_nonneg _ _ _ hu)).ne'
  have hp := @EReal.sub_pos (ent p e U) (ent q e (F.func '' U))
  have hn := EReal.sub_neg ht (Or.inl hb)
  refine ⟨hp,hn,?_⟩
  change _ - _ = 0 ↔ _
  exact ⟨fun h => le_antisymm (le_of_not_gt fun hl => (hp.mpr hl).ne' h)
    (le_of_not_gt fun hl => (hn.mpr hl).ne h),fun h => by
      rw [← h] at ht ⊢
      exact EReal.sub_self (ht.elim id id) hb⟩

theorem swap_strict :
    let act (f : Option Bool → Option Bool) (U : Set (Option Bool)) : Set Unit :=
      { _i | Active Swap.p f U }
    let ident (f : Option Bool → Option Bool) (U : Set (Option Bool)) : Set Unit :=
      { _i | Ident Swap.p f U }
    act (Swap.F * Swap.F).func Swap.U ⊂ act Swap.F.func Swap.U ∪ act Swap.F.func (Swap.F.func '' Swap.U) ∧
    ident Swap.F.func Swap.U ∩ ident Swap.F.func (Swap.F.func '' Swap.U) ⊂ ident (Swap.F * Swap.F).func Swap.U := by
  obtain ⟨a,b,c,d⟩ := Swap.calc_swap
  simp [Swap.image_dom.2,a,b,c,d]

theorem seven_readings :
    Seven.p false (some 2) (some 3) = 0 ∧ Seven.p true (some 2) (some 3) = 1 ∧
    Seven.p false (some 4) (some 5) = 1 := by norm_num [Seven.p,Seven.readout,liftDist,discrete,Fin.ext_iff]

theorem floor_type_spec {S : Set ℝ} (hs : S.Nonempty) :
    floorType S = channel (diamScale (fun _ : Unit => line id)) ⟨area S,hs.image some⟩
      (fun _ : Unit => line id) (run floorF).func 1 1 () () := rfl

theorem subfamily_partition (hd : ∀ i, ExtendedPseudoMetric X b (d i))
    {J : Set I} (hj : J.Nonempty) :
    (∀ S ∈ blocks (subD d J) F.func U, S.Nonempty) ∧
    ⋃₀ (blocks (subD d J) F.func U) = U ∧
    ∀ S ∈ blocks (subD d J) F.func U, ∀ T ∈ blocks (subD d J) F.func U,
      S = T ∨ Disjoint S T := by
  have h := subfamily_pseudometric_is_extended d J hj hd
  obtain ⟨ha,hb⟩ := fiber_cover (f := F.func) (U := U) h
  refine ⟨ha,hb,?_⟩
  rintro _ ⟨y,_,rfl⟩ _ ⟨z,_,rfl⟩
  exact fiber_disjoint h

theorem step_interval (y : ℝ) (hy : y ∈ punct) :
    legal (line id) (line id) (run step).func (area punct) (pt y) =
      Ioc 0 (ENNReal.ofReal |y|) := by
  rw [area_legal]
  ext r
  exact (step_legal hy).trans ⟨fun h => ⟨h.1.1,h.2⟩,
    fun h => ⟨⟨h.1,h.2.trans_lt ENNReal.ofReal_lt_top⟩,h.2⟩⟩

theorem scale_counter_domains :
    (area ({0} : Set ℝ)).Nonempty ∧ area ({0} : Set ℝ) ⊆ area ({0,1} : Set ℝ) ∧
    area ({0,1} : Set ℝ) ⊆ dom (run id) :=
  ⟨⟨pt 0,some_area.mpr rfl⟩, Set.image_mono (by simp),area_dom _ _⟩

theorem singleton_channel (i j : I) (e : ENNReal) :
    Defined (subD d {i}) (subD d {j}) F.func U e ↔ Defined (d i) (d j) F.func U e := by
  simp [subD,subfamily_pseudometric_singleton]

theorem singleton_delta (i j : I) (e : ENNReal)
    (hw : Defined (subD d {i}) (subD d {j}) F.func U e) :
    delta (subD d {i}) (subD d {j}) F.func U e hw =
    delta (d i) (d j) F.func U e ((singleton_channel i j e).mp hw) := by
  simp [delta,subD,subfamily_pseudometric_singleton]

theorem threshold_spec {S : Scale X I} (A : {A : Set X // A.Nonempty}) (_hA : A.val ⊆ dom F)
    {t u : ENNReal} (_ht : PosFin t) (_hu : PosFin u) (i j : I) :
    ((channel S A d F.func t u i j).1 = true ↔ S.val i A < t) ∧
    ((channel S A d F.func t u i j).2 = true ↔ u ≤ uniform (d i) (d j) F.func A A) := by
  simp [channel,bits,N]

theorem rad_notation {p q : D X} {y : X} {r : ENNReal} :
    r < rad p q F.func U y ↔ ∃ ρ, ρ ∈ legal p q F.func U y ∧ r < ρ := lt_sSup_iff

theorem zero_step (hd : ExtendedPseudoMetric X b (d i)) :
    ¬ Active (d i) (OperatorChain ([] : List (Op b))).func U :=
  chain_active hd []

theorem id_on_option (x : Option X) : (run id).func x = x := by cases x <;> rfl

theorem cut_alternatives {p q : D X} (hp : ExtendedPseudoMetric X b p)
    (hq : ExtendedPseudoMetric X b q) {x y : X} (hx : x ∈ U)
    (h : x ∈ fiber q F.func U (F.func y) ∨ p y x < rad p q F.func U y) :
    q (F.func y) (F.func x) = 0 := h.elim (fiber_cut hq) (point_cut hp hq hx)

theorem scalar_spec {H : Op (none : Option ℝ)} (hd : Rearrange.U ⊆ dom H) (L : ENNReal) :
    Rearrange.Lip H L ↔ HasScalarLipBound (fun _ : Unit => line id) H Rearrange.U () () L :=
  ⟨fun h => ⟨hd,h⟩,And.right⟩

theorem subfamily_constant_radii {J : Set I} (_hj : J.Nonempty) (_hu : U.Nonempty)
    (_hdom : U ⊆ dom F) (h : ∀ j ∈ J, Const (d j) F.func U) (i : I) :
    (∀ y ∈ U, rad (d i) (subD d J) F.func U y = ⊤) ∧
    uniform (d i) (subD d J) F.func U U = ⊤ := const_top (sub_const h)

end
end C3
