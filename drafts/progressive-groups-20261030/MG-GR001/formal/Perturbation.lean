import CompleteFamilies
import MatrixComparison

noncomputable section
open scoped BigOperators ENNReal NNReal Matrix.Norms.Operator
open Matrix
namespace MathGauge.RecursiveClosure.System
variable {Y V E I : Type} [Fintype V] [Fintype E] [Fintype I]
variable [DecidableEq V] [DecidableEq I] {g : Gauge Y I}
variable (s : System Y V E I g)

/-- Keep the graph, input sets, partition and routed call input literally the
same. Only the terminal value and return functions change. -/
def perturb (terminal : s.Family) (ret : E → Y → Y)
    (lip : ∀ e i x y, g.d i (ret e x) (ret e y) ≤
      ∑ j, (s.L e i j : ℝ≥0∞) * g.d j x y) : System Y V E I g where
  Input := s.Input
  src := s.src
  dst := s.dst
  step v x := match s.step v x with
    | .inl _ => .inl (terminal v x)
    | .inr ez => .inr ez
  step_src := by
    intro v x e z h
    cases he : s.step v x with
    | inl y => simp [he] at h
    | inr ez =>
      simp only [he] at h
      cases h
      exact s.step_src v x _ _ he
  ret := ret
  L := s.L
  lip := lip

theorem delta_triangle (F G H : s.Family) : s.delta F H ≤ s.delta F G + s.delta G H := by
  intro a
  exact iSup_le fun x => (g.triangle _ _ _ _).trans
    (add_le_add (s.point_le_delta F G _ _ x) (s.point_le_delta G H _ _ x))

variable (terminal : s.Family) (ret : E → Y → Y)
variable (lip : ∀ e i x y, g.d i (ret e x) (ret e y) ≤
  ∑ j, (s.L e i j : ℝ≥0∞) * g.d j x y)
variable (η : V × I → ℝ≥0)
variable (hstop : ∀ v x y, s.step v x = .inl y → ∀ i,
  g.d i y (terminal v x) ≤ η (v,i))
variable (hret : ∀ e y i, g.d i (s.ret e y) (ret e y) ≤ η (s.src e,i))

include hstop hret in
theorem perturb_local_bound (F : s.Family) :
    s.delta (s.transform F) ((s.perturb terminal ret lip).transform F) ≤ fun a => (η a : ℝ≥0∞) := by
  rintro ⟨v,i⟩
  apply iSup_le
  intro x
  cases hs : s.step v x with
  | inl y => simpa [transform,perturb,hs] using hstop v x y hs i
  | inr ez =>
    rcases ez with ⟨e,z⟩
    have he := s.step_src v x e z hs
    simpa [transform,perturb,hs,he] using hret e (F (s.dst e) z) i

include hstop hret in
theorem perturb_fixed_subsolution (F G : s.Family)
    (hF : s.transform F = F) (hG : (s.perturb terminal ret lip).transform G = G) :
    s.delta F G ≤ s.extendedCoeff *ᵥ s.delta F G + fun a => (η a : ℝ≥0∞) := by
  intro a
  calc
    s.delta F G a = s.delta (s.transform F) ((s.perturb terminal ret lip).transform G) a :=
      by rw [hF,hG]
    _ ≤ s.delta (s.transform F) (s.transform G) a +
        s.delta (s.transform G) ((s.perturb terminal ret lip).transform G) a :=
      s.delta_triangle _ _ _ a
    _ ≤ (s.extendedCoeff *ᵥ s.delta F G) a + η a := add_le_add
      (by simpa [s.gainAction_matrix] using s.delta_transform F G a)
      (s.perturb_local_bound terminal ret lip η hstop hret G a)

include hstop hret in
theorem perturb_inverse_bound [Nonempty V] [Nonempty I] [MetricSpace Y]
    (hd : ∀ x y, edist x y = ⨆ i, g.d i x y)
    (B : ℝ≥0) (hB : ∀ x y : Y, edist x y ≤ B)
    (hs : spectralRadius ℂ (complexMatrix s.coeff) < 1)
    (F G : s.Family) (hF : s.transform F = F)
    (hG : (s.perturb terminal ret lip).transform G = G) :
    (∀ a, s.delta F G a ≠ ⊤) ∧
    ∀ a, (s.delta F G a).toReal ≤
      (((1 - (Matrix.of (fun a b => (s.coeff a b : ℝ))))⁻¹ : Matrix (V × I) (V × I) ℝ) *ᵥ
        (fun a => (η a : ℝ))) a := by
  have hfinite : ∀ a, s.delta F G a ≠ ⊤ := by
    intro a
    apply ne_top_of_le_ne_top ENNReal.coe_ne_top
    apply iSup_le
    intro x
    apply le_trans _ (hB (F a.1 x) (G a.1 x))
    rw [hd]
    exact le_iSup (fun i => g.d i (F a.1 x) (G a.1 x)) a.2
  refine ⟨hfinite,?_⟩
  let d : V × I → ℝ≥0 := fun a => (s.delta F G a).toNNReal
  have hdcoe : ∀ a, (d a : ℝ≥0∞) = s.delta F G a :=
    fun a => ENNReal.coe_toNNReal (hfinite a)
  have he := s.perturb_fixed_subsolution terminal ret lip η hstop hret F G hF hG
  have he' : (fun a => (d a : ℝ)) ≤
      (fun a b => (s.coeff a b : ℝ)) *ᵥ (fun a => (d a : ℝ)) + fun a => (η a : ℝ) := by
    intro a
    have h := he a
    simp only [Matrix.mulVec, dotProduct, extendedCoeff, Pi.add_apply] at h ⊢
    simp only [← hdcoe, ← ENNReal.coe_mul, ← ENNReal.coe_finset_sum, ← ENNReal.coe_add] at h
    exact_mod_cast h
  obtain ⟨q,hq,hq1,w,hw,hb⟩ := positive_weights_of_spectral s.coeff hs
  have hh := inverse_comparison (fun a b => (s.coeff a b : ℝ))
    (fun a b => (s.coeff a b).coe_nonneg) (fun a => (w a : ℝ))
    (fun a => by exact_mod_cast hw a) (q : ℝ) (by exact_mod_cast hq1)
    (fun a => by simpa only [Matrix.mulVec, dotProduct] using (show (∑ j, (s.coeff a j : ℝ) * (w j : ℝ)) ≤ (q : ℝ) * (w a : ℝ) by exact_mod_cast hb a)) (fun a => (d a : ℝ)) (fun a => (η a : ℝ)) he'
  exact hh

end MathGauge.RecursiveClosure.System
