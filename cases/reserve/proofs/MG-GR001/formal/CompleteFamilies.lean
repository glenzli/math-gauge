import FiniteResidual
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.MetricSpace.Contracting

noncomputable section
open scoped BigOperators ENNReal NNReal UniformConvergence
open Filter Topology
namespace MathGauge.RecursiveClosure.System

variable {Y V E I : Type} [Fintype V] [Fintype E] [Fintype I]
variable [DecidableEq V] [DecidableEq I] {g : Gauge Y I}
variable (s : System Y V E I g) [MetricSpace Y]
variable (hd : ∀ x y, edist x y = ⨆ i, g.d i x y)
variable (w : V × I → ℝ≥0) (hw : ∀ a, 0 < w a)

/-- The metric is the stated weighted uniform distance on ALL families. -/
@[reducible] def familyEMetric : EMetricSpace s.Family where
  edist := s.weighted w
  edist_self := s.weighted_self w
  edist_comm := s.weighted_symm w
  edist_triangle := s.weighted_triangle w
  eq_of_edist_eq_zero := by
    intro F G h
    funext v x
    apply edist_eq_zero.mp
    rw [hd]
    apply le_antisymm (iSup_le fun i => ?_) bot_le
    simpa [h] using (s.point_le_delta F G v i x).trans
      (s.delta_le_weighted w hw F G (v,i))

def maxWeight : ℝ≥0 := Finset.univ.sup w
def maxInverseWeight : ℝ≥0 := Finset.univ.sup (fun a => (w a)⁻¹)

include hd hw in
theorem uniform_distance_le (F G : s.Family) :
    edist (UniformFun.ofFun (fun a : Sigma s.Input => F a.1 a.2))
      (UniformFun.ofFun (fun a : Sigma s.Input => G a.1 a.2)) ≤
      (maxWeight w : ℝ≥0∞) * s.weighted w F G := by
  apply iSup_le
  rintro ⟨v,x⟩
  rw [hd]
  apply iSup_le
  intro i
  have hw' : (w (v,i) : ℝ≥0∞) ≤ (maxWeight w : ℝ≥0∞) := by
    exact_mod_cast Finset.le_sup (f := w) (Finset.mem_univ (v,i))
  exact ((s.point_le_delta F G v i x).trans (s.delta_le_weighted w hw F G (v,i))).trans
    (by simpa [mul_comm] using mul_le_mul_left' hw' (s.weighted w F G))

include hd hw in
theorem weighted_le_uniform_distance (F G : s.Family) :
    s.weighted w F G ≤ (maxInverseWeight w : ℝ≥0∞) *
      edist (UniformFun.ofFun (fun a : Sigma s.Input => F a.1 a.2))
        (UniformFun.ofFun (fun a : Sigma s.Input => G a.1 a.2)) := by
  apply iSup_le
  intro a
  have hdelta : s.delta F G a ≤ edist
      (UniformFun.ofFun (fun b : Sigma s.Input => F b.1 b.2))
      (UniformFun.ofFun (fun b : Sigma s.Input => G b.1 b.2)) := by
    apply iSup_le
    intro x
    have hp : g.d a.2 (F a.1 x) (G a.1 x) ≤ edist (F a.1 x) (G a.1 x) := by
      rw [hd]; exact le_iSup (fun i => g.d i (F a.1 x) (G a.1 x)) a.2
    exact hp.trans
      (le_iSup (fun b : Sigma s.Input => edist (F b.1 b.2) (G b.1 b.2)) ⟨a.1,x⟩)
  have hinv : (w a : ℝ≥0∞)⁻¹ ≤ (maxInverseWeight w : ℝ≥0∞) := by
    rw [← ENNReal.coe_inv (hw a).ne']
    exact_mod_cast Finset.le_sup (f := fun a => (w a)⁻¹) (Finset.mem_univ a)
  simpa only [div_eq_mul_inv, mul_comm] using mul_le_mul hdelta hinv bot_le bot_le

/-- The equivalence derives completeness from the ordinary complete output
metric; no completeness or limit is stored as a certificate in the system. -/
def familyUniformEquiv :
    @UniformEquiv s.Family (Sigma s.Input →ᵤ Y)
      (s.familyEMetric hd w hw).toUniformSpace inferInstance := by
  letI := s.familyEMetric hd w hw
  letI : UniformSpace s.Family := (s.familyEMetric hd w hw).toUniformSpace
  refine { toFun := fun F => UniformFun.ofFun (fun a => F a.1 a.2)
           invFun := fun F v x => F ⟨v,x⟩
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           uniformContinuous_toFun := ?_
           uniformContinuous_invFun := ?_ }
  · exact (show LipschitzWith (maxWeight w)
        (fun F : s.Family => UniformFun.ofFun (fun a : Sigma s.Input => F a.1 a.2))
      from s.uniform_distance_le hd w hw).uniformContinuous
  · exact (show LipschitzWith (maxInverseWeight w)
        (fun F : Sigma s.Input →ᵤ Y => (fun v x => F ⟨v,x⟩ : s.Family))
      from fun F G => s.weighted_le_uniform_distance hd w hw _ _).uniformContinuous

theorem family_complete [CompleteSpace Y] :
    @CompleteSpace s.Family (s.familyEMetric hd w hw).toUniformSpace := by
  letI := s.familyEMetric hd w hw
  letI : UniformSpace s.Family := (s.familyEMetric hd w hw).toUniformSpace
  exact (s.familyUniformEquiv hd w hw).completeSpace_iff.mpr inferInstance

def branch (H : s.Family) : Set s.Family := {F | s.weighted w F H ≠ ⊤}

theorem branch_complete [CompleteSpace Y] (H : s.Family) :
    @IsComplete s.Family (s.familyEMetric hd w hw).toUniformSpace (s.branch w H) := by
  letI := s.familyEMetric hd w hw
  letI : UniformSpace s.Family := (s.familyEMetric hd w hw).toUniformSpace
  letI := s.family_complete hd w hw
  change IsComplete {F : s.Family | edist F H ≠ ⊤}
  simpa only [Metric.eball, ← lt_top_iff_ne_top] using
    (Metric.isClosed_eball_top (x := H)).isComplete

theorem branch_invariant (q : ℝ≥0)
    (hc : ∀ F G : s.Family, s.weighted w (s.transform F) (s.transform G) ≤
      q * s.weighted w F G)
    (H : s.Family) (hR : s.weighted w (s.transform H) H ≠ ⊤) :
    Set.MapsTo s.transform (s.branch w H) (s.branch w H) := by
  intro F hF
  apply ne_top_of_le_ne_top _ (s.weighted_triangle w (s.transform F) (s.transform H) H)
  exact ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hF) (hc F H), hR⟩

include hd hw in
theorem branch_fixed [CompleteSpace Y] (q : ℝ≥0) (hq : q < 1)
    (hc : ∀ F G : s.Family, s.weighted w (s.transform F) (s.transform G) ≤
      q * s.weighted w F G)
    (H₀ : s.Family) (hR : s.weighted w (s.transform H₀) H₀ ≠ ⊤) :
    ∃ F : s.Family, s.transform F = F ∧ F ∈ s.branch w H₀ ∧
      (∀ G ∈ s.branch w H₀, s.transform G = G → G = F) ∧
      ∀ H ∈ s.branch w H₀, ∀ n : ℕ,
        s.weighted w (s.transform^[n] H) F ≤ (q : ℝ≥0∞)^n *
          (s.weighted w H H₀ + s.weighted w (s.transform H₀) H₀ / (1-q)) := by
  letI := s.familyEMetric hd w hw
  letI : UniformSpace s.Family := (s.familyEMetric hd w hw).toUniformSpace
  letI := s.family_complete hd w hw
  have hcontract : ContractingWith q s.transform := ⟨hq,hc⟩
  have hR' : edist H₀ (s.transform H₀) ≠ ⊤ := by
    change s.weighted w H₀ (s.transform H₀) ≠ ⊤
    rwa [s.weighted_symm]
  let F := hcontract.efixedPoint s.transform H₀ hR'
  have hfix : s.transform F = F := hcontract.efixedPoint_isFixedPt hR'
  have hdist : s.weighted w H₀ F ≤ s.weighted w (s.transform H₀) H₀ / (1-q) := by
    have hh := hcontract.edist_efixedPoint_le hR'
    change s.weighted w H₀ F ≤ s.weighted w H₀ (s.transform H₀) / (1-q) at hh
    rwa [s.weighted_symm w H₀ (s.transform H₀)] at hh
  have hmem : F ∈ s.branch w H₀ := by
    change edist F H₀ ≠ ⊤
    rw [edist_comm]
    exact (hcontract.edist_efixedPoint_lt_top hR').ne
  refine ⟨F,hfix,hmem,?_,?_⟩
  · intro G hG hfixG
    apply (hcontract.eq_or_edist_eq_top_of_fixedPoints hfixG hfix).resolve_right
    apply ne_top_of_le_ne_top _ (s.weighted_triangle w G H₀ F)
    exact ENNReal.add_ne_top.mpr ⟨hG,by simpa only [s.weighted_symm w H₀ F] using hmem⟩
  · intro H hH n
    have hi := s.weighted_iterate q w hc H F n
    rw [Function.IsFixedPt.iterate hfix n] at hi
    exact hi.trans (mul_le_mul_left' ((s.weighted_triangle w H H₀ F).trans
      (add_le_add_right hdist _)) _)

include hw in
theorem max_delta_le_weighted (F G : s.Family) :
    (⨆ a, s.delta F G a) ≤ (maxWeight w : ℝ≥0∞) * s.weighted w F G := by
  apply iSup_le
  intro a
  have hwa : (w a : ℝ≥0∞) ≤ (maxWeight w : ℝ≥0∞) := by
    exact_mod_cast Finset.le_sup (f := w) (Finset.mem_univ a)
  exact (s.delta_le_weighted w hw F G a).trans
    (by simpa [mul_comm] using mul_le_mul_right hwa (s.weighted w F G))

include hd hw in
theorem bounded_weighted_finite (B : ℝ≥0) (hB : ∀ x y : Y, edist x y ≤ B)
    (F G : s.Family) : s.weighted w F G ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (s.weighted_le_uniform_distance hd w hw F G)
  apply ENNReal.mul_ne_top ENNReal.coe_ne_top
  exact ne_top_of_le_ne_top ENNReal.coe_ne_top (iSup_le fun a => hB _ _)

include hd hw in
theorem bounded_fixed [Nonempty Y] [CompleteSpace Y]
    (B : ℝ≥0) (hB : ∀ x y : Y, edist x y ≤ B)
    (q : ℝ≥0) (hq : q < 1)
    (hc : ∀ F G : s.Family, s.weighted w (s.transform F) (s.transform G) ≤
      q * s.weighted w F G) :
    ∃ F : s.Family, s.transform F = F ∧
      (∀ G : s.Family, s.transform G = G → G = F) ∧
      ∀ H : s.Family, ∃ C : ℝ≥0, ∀ n : ℕ,
        (⨆ a, s.delta (s.transform^[n] H) F a) ≤ (C : ℝ≥0∞) * (q : ℝ≥0∞)^n := by
  let H₀ : s.Family := fun _ _ => Classical.choice ‹Nonempty Y›
  obtain ⟨F,hfix,hmem,huniq,hbound⟩ := s.branch_fixed hd w hw q hq hc H₀
    (s.bounded_weighted_finite hd w hw B hB _ _)
  refine ⟨F,hfix,fun G hG => huniq G (s.bounded_weighted_finite hd w hw B hB _ _) hG,?_⟩
  intro H
  have hfinite := s.bounded_weighted_finite hd w hw B hB H F
  refine ⟨maxWeight w * (s.weighted w H F).toNNReal,fun n => ?_⟩
  have hi := s.weighted_iterate q w hc H F n
  rw [Function.IsFixedPt.iterate hfix n] at hi
  calc
    (⨆ a, s.delta (s.transform^[n] H) F a) ≤
        (maxWeight w : ℝ≥0∞) * s.weighted w (s.transform^[n] H) F :=
      s.max_delta_le_weighted w hw _ _
    _ ≤ (maxWeight w : ℝ≥0∞) * ((q : ℝ≥0∞)^n * s.weighted w H F) :=
      mul_le_mul_right hi _
    _ = _ := by simp [ENNReal.coe_toNNReal hfinite, mul_assoc, mul_comm, mul_left_comm]

theorem branch_pair_finite (H₀ F G : s.Family)
    (hF : F ∈ s.branch w H₀) (hG : G ∈ s.branch w H₀) :
    s.weighted w F G ≠ ⊤ := by
  apply ne_top_of_le_ne_top _ (s.weighted_triangle w F H₀ G)
  exact ENNReal.add_ne_top.mpr ⟨hF,by simpa only [s.weighted_symm w H₀ G] using hG⟩

include hd hw in
theorem branch_fixed_max_bound [CompleteSpace Y] (q : ℝ≥0) (hq : q < 1)
    (hc : ∀ F G : s.Family, s.weighted w (s.transform F) (s.transform G) ≤
      q * s.weighted w F G)
    (H₀ : s.Family) (hR : s.weighted w (s.transform H₀) H₀ ≠ ⊤) :
    ∃ F : s.Family, s.transform F = F ∧ F ∈ s.branch w H₀ ∧
      (∀ G ∈ s.branch w H₀, s.transform G = G → G = F) ∧
      ∀ H ∈ s.branch w H₀, ∃ C : ℝ≥0, ∀ n : ℕ,
        (⨆ a, s.delta (s.transform^[n] H) F a) ≤ (C : ℝ≥0∞) * (q : ℝ≥0∞)^n := by
  obtain ⟨F,hF,hmem,hu,he⟩ := s.branch_fixed hd w hw q hq hc H₀ hR
  refine ⟨F,hF,hmem,hu,?_⟩
  intro H hH
  have hfinite := s.branch_pair_finite w H₀ H F hH hmem
  refine ⟨maxWeight w * (s.weighted w H F).toNNReal,fun n => ?_⟩
  have hi := s.weighted_iterate q w hc H F n
  rw [Function.IsFixedPt.iterate hF n] at hi
  calc
    (⨆ a, s.delta (s.transform^[n] H) F a) ≤
        (maxWeight w : ℝ≥0∞) * s.weighted w (s.transform^[n] H) F :=
      s.max_delta_le_weighted w hw _ _
    _ ≤ (maxWeight w : ℝ≥0∞) * ((q : ℝ≥0∞)^n * s.weighted w H F) :=
      mul_le_mul_right hi _
    _ = _ := by simp [ENNReal.coe_toNNReal hfinite,mul_assoc,mul_comm,mul_left_comm]

include hd in
theorem spectral_bounded_fixed [Nonempty V] [Nonempty I] [Nonempty Y] [CompleteSpace Y]
    (B : ℝ≥0) (hB : ∀ x y : Y, edist x y ≤ B)
    (hs : spectralRadius ℂ (complexMatrix s.coeff) < 1) :
    ∃ q : ℝ≥0, 0 < q ∧ q < 1 ∧ ∃ F : s.Family,
      s.transform F = F ∧ (∀ G : s.Family, s.transform G = G → G = F) ∧
      ∀ H : s.Family, ∃ C : ℝ≥0, ∀ n : ℕ,
        (⨆ a, s.delta (s.transform^[n] H) F a) ≤ (C : ℝ≥0∞) * (q : ℝ≥0∞)^n := by
  obtain ⟨q,hq,hq1,w,hw,hb⟩ := positive_weights_of_spectral s.coeff hs
  exact ⟨q,hq,hq1,s.bounded_fixed hd w hw B hB q hq1
    (s.weighted_contraction q w hw hb)⟩

end MathGauge.RecursiveClosure.System
