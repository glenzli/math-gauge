import DeepCongruence

noncomputable section
namespace MathGauge.GR020.PadicParameter
open MathGauge.PadicOrthogonal
local notation "Z₂" => ℤ_[2]
abbrev M := Mat Z₂ 2

def even (c : Z₂) : Prop := c ∈ Ideal.span {(2 : Z₂)}

theorem denominator_unit (c : Z₂) (hc : even c) : IsUnit (1+c^2) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro h
  have hc' : c ∈ IsLocalRing.maximalIdeal Z₂ := by
    simpa only [PadicInt.maximalIdeal_eq_span_p] using hc
  have hcc : c^2 ∈ IsLocalRing.maximalIdeal Z₂ := by
    simpa only [pow_two] using (IsLocalRing.maximalIdeal Z₂).mul_mem_left c hc'
  have hh := (IsLocalRing.maximalIdeal Z₂).sub_mem h hcc
  have h1 : (1 : Z₂) ∈ IsLocalRing.maximalIdeal Z₂ := by simpa using hh
  exact (IsLocalRing.notMem_maximalIdeal.mpr isUnit_one) h1

def inverseDenom (c : Z₂) (hc : even c) : Z₂ := ↑((denominator_unit c hc).unit⁻¹)

theorem denominator_inverse (c : Z₂) (hc : even c) : (1+c^2)*inverseDenom c hc=1 := by
  simp [inverseDenom]

def P : M := !![1,0;0,0]
def Q (c : Z₂) (hc : even c) : M :=
  !![inverseDenom c hc, c*inverseDenom c hc;
     c*inverseDenom c hc, c^2*inverseDenom c hc]
def V (c : Z₂) : M := !![1,-c;c,1]
def W (c : Z₂) (hc : even c) : M :=
  !![inverseDenom c hc,c*inverseDenom c hc;
     -(c*inverseDenom c hc),inverseDenom c hc]

theorem P_symmetric : P.transpose=P := by ext i j; fin_cases i <;> fin_cases j <;> rfl
theorem P_idempotent : P*P=P := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [P,Matrix.mul_apply,Fin.sum_univ_two]

theorem Q_symmetric (c : Z₂) (hc : even c) : (Q c hc).transpose=Q c hc := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem Q_idempotent (c : Z₂) (hc : even c) : Q c hc*Q c hc=Q c hc := by
  have hs := denominator_inverse c hc
  ext i j; fin_cases i <;> fin_cases j <;> simp [Q,Matrix.mul_apply,Fin.sum_univ_two]
  · linear_combination inverseDenom c hc*hs
  · linear_combination c*inverseDenom c hc*hs
  · linear_combination c*inverseDenom c hc*hs
  · linear_combination c^2*inverseDenom c hc*hs

theorem V_W (c : Z₂) (hc : even c) : V c*W c hc=1 := by
  have hs := denominator_inverse c hc
  ext i j; fin_cases i <;> fin_cases j <;> simp [V,W,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals first | (solve | ring) | (solve | linear_combination hs)

theorem W_V (c : Z₂) (hc : even c) : W c hc*V c=1 := by
  have hs := denominator_inverse c hc
  ext i j; fin_cases i <;> fin_cases j <;> simp [V,W,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals first | (solve | ring) | (solve | linear_combination hs)

def Vunit (c : Z₂) (hc : even c) : Mˣ := ⟨V c,W c hc,V_W c hc,W_V c hc⟩

theorem V_intertwines (c : Z₂) (hc : even c) : V c*P=Q c hc*V c := by
  have hs := denominator_inverse c hc
  ext i j; fin_cases i <;> fin_cases j <;> simp [P,Q,V,Matrix.mul_apply,Fin.sum_univ_two]
  · linear_combination -hs
  · ring
  · linear_combination -c*hs
  · ring

theorem V_gram (c : Z₂) : (V c).transpose*V c=(1+c^2) • (1 : M) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [V,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem V_near (c : Z₂) (hc : even c) : Near (IsLocalRing.maximalIdeal Z₂) (V c) 1 := by
  intro i j
  have hc' : c ∈ IsLocalRing.maximalIdeal Z₂ := by
    simpa only [PadicInt.maximalIdeal_eq_span_p] using hc
  fin_cases i <;> fin_cases j <;> simp [V,hc',(IsLocalRing.maximalIdeal Z₂).neg_mem hc']

def datum (c : Z₂) (hc : even c) : ComparisonData Z₂ (IsLocalRing.maximalIdeal Z₂) 2 2 where
  source := complementary P
  target := complementary (Q c hc)
  source_valid := complementary_valid P P_symmetric P_idempotent
  target_valid := complementary_valid (Q c hc) (Q_symmetric c hc) (Q_idempotent c hc)
  comparison := Vunit c hc
  near_identity := V_near c hc
  intertwines := by
    intro i; fin_cases i
    · exact V_intertwines c hc
    · simpa [complementary,mul_sub,sub_mul] using
        congrArg (fun A : M => V c-A) (V_intertwines c hc)

theorem first_column_constraint (c : Z₂) (hc : even c) (U : M)
    (hi : U*P=Q c hc*U) : U 1 0=c*U 0 0 := by
  have ha := congrFun (congrFun hi 0) 0
  have hb := congrFun (congrFun hi 1) 0
  simp [P,Q,Matrix.mul_apply,Fin.sum_univ_two] at ha hb
  linear_combination hb-c*ha

theorem norm_constraint (c : Z₂) (hc : even c) (U : M)
    (hu : U.transpose*U=1) (hi : U*P=Q c hc*U) : (1+c^2)*(U 0 0)^2=1 := by
  have hn := congrFun (congrFun hu 0) 0
  simp [Matrix.mul_apply,Fin.sum_univ_two,first_column_constraint c hc U hi] at hn
  linear_combination hn

theorem mod_eight_obstruction : ∀ x y : ZMod 8, (1+x^2)*y^2=1 →
    ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) x=0 := by decide

/-- This excludes every orthogonal intertwiner, without assuming near identity. -/
theorem necessary_four (c : Z₂) (hc : even c) (U : M)
    (hu : U.transpose*U=1) (hi : U*P=Q c hc*U) : c ∈ Ideal.span {(4 : Z₂)} := by
  have hn := congrArg (PadicInt.toZModPow (p := 2) 3) (norm_constraint c hc U hu hi)
  have he : (1+(PadicInt.toZModPow 3 c)^2)*(PadicInt.toZModPow 3 (U 0 0))^2=1 := by
    simpa only [map_mul,map_add,map_one,map_pow] using hn
  have hc8 := mod_eight_obstruction (PadicInt.toZModPow 3 c) (PadicInt.toZModPow 3 (U 0 0)) he
  have hc4 : PadicInt.toZModPow (p := 2) 2 c=0 := by
    have hcast := PadicInt.cast_toZModPow (p := 2) 2 3 (by decide) c
    exact hcast.symm.trans hc8
  have hk : c ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 2) := hc4
  rw [PadicInt.ker_toZModPow] at hk
  norm_num only [show (2 : Z₂)^2=4 by ring] at hk
  exact hk

/-- For c=4k the actual Gram matrix is 1-4T with T=-4k² I.
The already proved integral iteration constructs its root and U. -/
theorem sufficient_four (c : Z₂) (hc : even c) (h4 : c ∈ Ideal.span {(4 : Z₂)}) :
    HasIsometricComparison (datum c hc) := by
  obtain ⟨k,hk⟩ := Ideal.mem_span_singleton.mp h4
  let T : M := algebraMap Z₂ M (-4*k^2)
  have hT : Near (IsLocalRing.maximalIdeal Z₂) T 0 := by
    intro i j
    rw [PadicInt.maximalIdeal_eq_span_p,Ideal.mem_span_singleton]
    dsimp [T]
    rw [Algebra.algebraMap_eq_smul_one]
    by_cases hij : i=j
    · subst j
      refine ⟨-2*k^2,?_⟩
      simp
      ring
    · simp [Matrix.one_apply,hij]
  have hs : T.transpose=T := by simp [T,Algebra.algebraMap_eq_smul_one]
  have hcentral : ∀ i, Commute T ((datum c hc).source i) := by
    intro i
    exact Algebra.commute_algebraMap_left _ _
  have hGram : (Vunit c hc : M).transpose*(Vunit c hc : M)=1-4*T := by
    change (V c).transpose*V c=1-4*T
    rw [V_gram,hk]
    ext i j
    change ((1+(4*k)^2) • (1 : M)) i j=(1-4*algebraMap Z₂ M (-4*k^2)) i j
    rw [Matrix.sub_apply]
    change ((1+(4*k)^2) • (1 : M)) i j=(1 : M) i j-
      ((((4 : ℕ) : M)*algebraMap Z₂ M (-4*k^2)) i j)
    rw [numeral_mul_entry,Algebra.algebraMap_eq_smul_one]
    simp
    ring
  obtain ⟨U,hn,hu,hi⟩ := normalize_adic (IsLocalRing.maximalIdeal Z₂)
    (Vunit c hc) (datum c hc).source (datum c hc).target (datum c hc).intertwines
    T hT hs hcentral hGram (V_near c hc)
  exact ⟨U,hn,hu,hi⟩

/-- S6: exact classification, with genuine data on both sides and an
all-matrices impossibility theorem for c∉4ℤ₂. -/
theorem classification (c : Z₂) (hc : even c) :
    HasIsometricComparison (datum c hc) ↔ c ∈ Ideal.span {(4 : Z₂)} := by
  constructor
  · rintro ⟨U,_,hu,hi⟩
    exact necessary_four c hc (U : M) hu (hi 0)
  · exact sufficient_four c hc

end MathGauge.GR020.PadicParameter
