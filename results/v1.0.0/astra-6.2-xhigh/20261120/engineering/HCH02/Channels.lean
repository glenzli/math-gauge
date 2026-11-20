import Bounds
import Mathlib.Data.ENNReal.Inv

open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators Classical
noncomputable section
namespace HCH02

variable {I X : Type} {b : X}
abbrev Channel (I : Type) := I × I
def Row (A : Mat I) (i j : I) := ∀ k, k ≠ i → A k j = 0
def Col (A : Mat I) (i j : I) := ∀ k, k ≠ j → A i k = 0
def Diagonal (A : Mat I) := ∀ i j, i ≠ j → A i j = 0

variable [Fintype I] [Nonempty I]
def RowDec (g : Gauge X I b) (p : Operator X b) (U : Set X) (j : I) :=
  ∃ A ∈ lip g p U, ∃ i, Row A i j
def ColDec (g : Gauge X I b) (p : Operator X b) (U : Set X) (i : I) :=
  ∃ A ∈ lip g p U, ∃ j, Col A i j

abbrev Region (p : Operator X b) := {U : Set X // U ⊆ dom p}

def scalars (g : Gauge X I b) (p : Operator X b) (U : Region p) (i j : I) : Set ENNReal :=
  {r | ∀ x ∈ U.val, ∀ y ∈ U.val, g.d j (p.func x) (p.func y) ≤ r * g.d i x y}

def best (g : Gauge X I b) (p : Operator X b) (U : Region p) (i j : I) :=
  sInf (scalars g p U i j)

section Scalar
variable {g : Gauge X I b} {p : Operator X b} {U : Region p} {i j : I}
local notation "S" => scalars g p U i j
local notation "a" => best g p U i j

theorem best_empty (h : S = ∅) : a = ⊤ := by simp [best, h]

theorem obstructed {x y} (hx : x ∈ U.val) (hy : y ∈ U.val)
    (hz : g.d i x y = 0) (hp : 0 < g.d j (p.func x) (p.func y)) : S = ∅ ∧ a = ⊤ := by
  have he : S = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun r hr => by
    have h := hr x hx y hy
    rw [hz, mul_zero] at h
    exact hp.not_ge h
  exact ⟨he, best_empty he⟩

theorem scalar_up {r t : ENNReal} (hr : r ∈ S) (ht : r ≤ t) : t ∈ S :=
  fun x hx y hy => (hr x hx y hy).trans (mul_le_mul_left ht _)

theorem above_best {r : ENNReal} (h : a < r) : r ∈ S := by
  obtain ⟨t, ht, htr⟩ := sInf_lt_iff.mp h
  exact scalar_up ht htr.le

theorem zero_best {r : ENNReal} (h : a = 0) (hr : 0 < r) : r ∈ S :=
  above_best (h ▸ hr)

theorem finite_iff : a < ⊤ ↔ ∃ r ∈ S, r < ⊤ := sInf_lt_iff

theorem attained (hp : 0 < a) (hf : a < ⊤) : a ∈ S := by
  obtain ⟨r, hr, _⟩ := finite_iff.mp hf
  have hn : (⨅ t : S, (t : ENNReal)) ≠ 0 := by
    simpa only [best, sInf_eq_iInf'] using hp.ne'
  intro x hx y hy
  rw [best, sInf_eq_iInf', ENNReal.iInf_mul' (fun _ h => (hn h).elim) (fun _ => ⟨⟨r,hr⟩⟩)]
  exact le_iInf fun t => t.property x hx y hy

end Scalar

def discreteD (x y : Fin 3) : ENNReal := if x = y then 0 else ⊤

def exampleGauge : Gauge (Fin 3) Unit 0 where
  d _ := discreteD
  metric _ := {
    nonabsorbing := ⟨1, by decide⟩
    dist_self := by simp [discreteD]
    symm := by intro x y; simp [discreteD, eq_comm]
    triangle := by intro x y z; by_cases h : x = y <;> simp_all [discreteD]
    isolate_bot := by intro x hx; simp [discreteD, hx] }

def exampleId : Operator (Fin 3) 0 := ⟨id, rfl⟩
def exampleU : Region exampleId := ⟨dom exampleId, fun _ h => h⟩

theorem unattained_zero : exampleU.val.Nonempty ∧ best exampleGauge exampleId exampleU () () = 0 ∧
    0 ∉ scalars exampleGauge exampleId exampleU () () := by
  have h₁ : (1 : Fin 3) ∈ exampleU.val := by change (1 : Fin 3) ≠ 0; decide
  have h₂ : (2 : Fin 3) ∈ exampleU.val := by change (2 : Fin 3) ≠ 0; decide
  have pos_mem {r : ENNReal} (hr : 0 < r) : r ∈ scalars exampleGauge exampleId exampleU () () := by
    intro x _ y _
    by_cases h : x = y <;> simp [exampleGauge, exampleId, discreteD, h, ENNReal.mul_top, hr.ne']
  refine ⟨⟨1,h₁⟩, ?_, ?_⟩
  · by_contra hn
    obtain ⟨r, hr, hlt⟩ := exists_between (pos_iff_ne_zero.mpr hn)
    exact hlt.not_ge (sInf_le (pos_mem hr))
  · intro hz
    have h := hz 1 h₁ 2 h₂
    have hne : (1 : Fin 3) ≠ 2 := by decide
    simp [exampleGauge, exampleId, discreteD, hne] at h

variable {g : Gauge X I b} {p : Operator X b} {U : Set X} {A K : Mat I} {i j : I} {x y : X}

omit [Nonempty I] in
theorem erase_term (h : A i j = 0) (v : I → ENNReal) :
    A i j * v i = 0 ∧ act A v j = ∑ k ∈ Finset.univ.erase i, A k j * v k := by
  refine ⟨by simp [h], ?_⟩
  have he := Finset.add_sum_erase Finset.univ (fun k => A k j * v k) (Finset.mem_univ i)
  simpa [act, h] using he.symm

theorem lip_erase (ha : A ∈ lip g p U) (h : A i j = 0) (hx : x ∈ U) (hy : y ∈ U) :
    A i j * g.d i x y = 0 ∧
    g.d j (p.func x) (p.func y) ≤ ∑ k ∈ Finset.univ.erase i, A k j * g.d k x y := by
  obtain ⟨hz, he⟩ := erase_term h (vec g x y)
  exact ⟨hz, (ha.2 x hx y hy j).trans_eq he⟩

theorem row_bound (ha : A ∈ lip g p U) (h : Row A i j) (hx : x ∈ U) (hy : y ∈ U) :
    g.d j (p.func x) (p.func y) ≤ A i j * g.d i x y := by
  apply (ha.2 x hx y hy j).trans_eq
  exact Finset.sum_eq_single_of_mem i (Finset.mem_univ i) (fun k _ hk => by simp [h k hk])

omit [Fintype I] [Nonempty I] in
theorem col_term (hc : Col A i j) {k : I} (hk : k ≠ j) (v : I → ENNReal) :
    A i k * v i = 0 := by rw [hc k hk, zero_mul]

theorem column_contribution (_ha : A ∈ lip g p U) (hc : Col A i j)
    (_hx : x ∈ U) (_hy : y ∈ U) {k : I} (hk : k ≠ j) : A i k * g.d i x y = 0 :=
  col_term hc hk (vec g x y)

theorem diagonal_upper (ha : A ∈ lip g p U) (hd : Diagonal A) (j : I)
    (hx : x ∈ U) (hy : y ∈ U) :
    g.d j (p.func x) (p.func y) ≤ A j j * g.d j x y :=
  row_bound ha (fun k hk => hd k j hk) hx hy

def ScalarBounds (g : Gauge X I b) (p : Operator X b) (U : Set X)
    (j : I) (lo hi : ENNReal) := ∀ x ∈ U, ∀ y ∈ U,
  lo * g.d j x y ≤ g.d j (p.func x) (p.func y) ∧ g.d j (p.func x) (p.func y) ≤ hi * g.d j x y

theorem bilateral (ha : A ∈ lip g p U) (hk : K ∈ coLip g p U) (h : Row A j j) :
    ScalarBounds g p U j (K j j) (A j j) :=
  fun _ hx _ hy => ⟨co_term hk hx hy j j, row_bound ha h hx hy⟩

theorem all_bilateral (ha : A ∈ lip g p U) (hk : K ∈ coLip g p U) (h : ∀ j, Row A j j) :
    ∀ j, ScalarBounds g p U j (K j j) (A j j) := fun j => bilateral ha hk (h j)

theorem finite_bilateral (ha : A ∈ lip g p U) (hk : K ∈ coLip g p U) (h : ∀ j, Row A j j)
    (hf : ∀ j, K j j < ⊤ ∧ A j j < ⊤) (j : I) : ∃ lo hi : NNReal,
    (lo : ENNReal) = K j j ∧ (hi : ENNReal) = A j j ∧ ScalarBounds g p U j lo hi := by
  refine ⟨(K j j).toNNReal, (A j j).toNNReal, ?_⟩
  simp only [ENNReal.coe_toNNReal (hf j).1.ne, ENNReal.coe_toNNReal (hf j).2.ne, true_and]
  exact all_bilateral ha hk h j

theorem distinguish (hk : K ∈ coLip g p U) (h : 0 < K i j) (hx : x ∈ U) (hy : y ∈ U)
    (hd : 0 < g.d i x y) : 0 < g.d j (p.func x) (p.func y) :=
  (pos_iff_ne_zero.mpr (mul_ne_zero h.ne' hd.ne')).trans_le (co_term hk hx hy i j)

theorem reflect_zero (hk : K ∈ coLip g p U) (h : ∀ j, 0 < K j j) (hx : x ∈ U) (hy : y ∈ U)
    (hz : GaugeZeroRelated g.d (p.func x) (p.func y)) : GaugeZeroRelated g.d x y := by
  intro j
  by_contra hn
  exact (distinguish hk (h j) hx hy (pos_iff_ne_zero.mpr hn)).ne' (hz j)

end HCH02
