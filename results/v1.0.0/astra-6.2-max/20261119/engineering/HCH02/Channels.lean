import Bounds
import Mathlib.Data.ENNReal.Inv

namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal NNReal Classical
noncomputable section

variable {X I : Type} {b : X} [Fintype I] [Nonempty I]
variable (G : Gauge X I b) (f : Operator X b) (U : Set X)

abbrev Channel (I : Type) := I × I

def feasible (i j : I) : Set ℝ≥0∞ :=
  {c | U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    G.d j (f.func x) (f.func y) ≤ c * G.d i x y}

def best (i j : I) := sInf (feasible G f U i j)

variable {G f U} {i j : I} {x y : X} {a c : ℝ≥0∞}

theorem feasible_iff (hU : U ⊆ dom f) :
    c ∈ feasible G f U i j ↔ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
      G.d j (f.func x) (f.func y) ≤ c * G.d i x y :=
  ⟨And.right, fun h => ⟨hU, h⟩⟩

theorem best_empty (h : feasible G f U i j = ∅) : best G f U i j = ⊤ := by
  simp [best, h]

theorem empty_channel (hx : x ∈ U) (hy : y ∈ U) (hz : G.d i x y = 0)
    (hp : 0 < G.d j (f.func x) (f.func y)) :
    feasible G f U i j = ∅ ∧ best G f U i j = ⊤ := by
  have e : feasible G f U i j = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro c hc
    have h := hc.2 hx hy
    rw [hz, mul_zero] at h
    exact hp.not_ge h
  exact ⟨e, best_empty e⟩

theorem feasible_up (ha : a ∈ feasible G f U i j) (h : a ≤ c) :
    c ∈ feasible G f U i j :=
  ⟨ha.1, fun {_ _} hx hy => (ha.2 hx hy).trans (mul_le_mul_left h _)⟩

theorem above_best (h : best G f U i j < c) : c ∈ feasible G f U i j := by
  obtain ⟨a, ha, hac⟩ := sInf_lt_iff.mp h
  exact feasible_up ha hac.le

theorem best_attained (hp : 0 < best G f U i j) (hf : best G f U i j < ⊤) :
    best G f U i j ∈ feasible G f U i j := by
  have ht := above_best hf
  refine ⟨ht.1, fun {x y} hx hy => ?_⟩
  by_cases hz : G.d i x y = 0
  · simpa [hz] using ht.2 hx hy
  by_cases htop : G.d i x y = ⊤
  · simp [htop, ENNReal.mul_top hp.ne']
  apply (ENNReal.div_le_iff hz htop).mp
  exact le_sInf fun c hc => (ENNReal.div_le_iff hz htop).mpr (hc.2 hx hy)

theorem zero_best (h : best G f U i j = 0) (hc : 0 < c) (_hf : c < ⊤) :
    c ∈ feasible G f U i j := above_best (h ▸ hc)

theorem finite_iff : best G f U i j < ⊤ ↔ ∃ c ∈ feasible G f U i j, c < ⊤ :=
  sInf_lt_iff

def discreteGauge : Gauge (Fin 3) Unit 0 where
  d _ x y := if x = y then 0 else ⊤
  metric _ := {
    nonabsorbing := ⟨1, by decide⟩
    dist_self := by simp
    symm := by intro x y; simp [eq_comm]
    triangle := by
      intro x y z
      by_cases h : x = y
      · subst y; simp
      · simp [h]
    isolate_bot := by intro x h; simp [h] }

theorem zero_unattained :
    let f := ident (0 : Fin 3)
    let U := dom f
    U.Nonempty ∧ U ⊆ dom f ∧ best discreteGauge f U () () = 0 ∧
      0 ∉ feasible discreteGauge f U () () := by
  dsimp only
  let f := ident (0 : Fin 3)
  have hp {c : ℝ≥0∞} (hc : 0 < c) : c ∈ feasible discreteGauge f (dom f) () () := by
    refine ⟨Set.Subset.rfl, fun {x y} _ _ => ?_⟩
    by_cases he : x = y <;> simp [discreteGauge, f, ident, he, ENNReal.mul_top hc.ne']
  have h1 : (1 : Fin 3) ∈ dom f := by change (1 : Fin 3) ≠ 0; decide
  have h2 : (2 : Fin 3) ∈ dom f := by change (2 : Fin 3) ≠ 0; decide
  refine ⟨⟨1, h1⟩, Set.Subset.rfl, le_antisymm ?_ (zero_le _), ?_⟩
  · by_contra! h
    obtain ⟨c, hc, hlt⟩ := exists_between h
    exact hlt.not_ge (sInf_le (hp hc))
  · intro hz
    have h := hz.2 h1 h2
    have he : (1 : Fin 3) ≠ 2 := by decide
    simp [discreteGauge, ident, he] at h

def Row (L : Coeff I) (i j : I) := ∀ k, k ≠ i → L k j = 0
def Col (L : Coeff I) (i j : I) := ∀ k, k ≠ j → L i k = 0
def Diagonal (L : Coeff I) := ∀ i j, i ≠ j → L i j = 0

def RowDecoupled (G : Gauge X I b) (f : Operator X b) (U : Set X) (j : I) :=
  ∃ L ∈ lip G f U, ∃ i, Row L i j
def ColDecoupled (G : Gauge X I b) (f : Operator X b) (U : Set X) (i : I) :=
  ∃ L ∈ lip G f U, ∃ j, Col L i j

variable {L K : Coeff I}

omit [Nonempty I] in
theorem erase_input (v : I → ℝ≥0∞) (h : L i j = 0) :
    L i j * v i = 0 ∧ act L v j = ∑ k ∈ Finset.univ.erase i, L k j * v k := by
  refine ⟨by simp [h], ?_⟩
  simpa [act, h] using
    (Finset.univ.add_sum_erase (fun k => L k j * v k) (Finset.mem_univ i)).symm

theorem erase_upper (hL : L ∈ lip G f U) (h : L i j = 0) (hx : x ∈ U) (hy : y ∈ U) :
    G.d j (f.func x) (f.func y) ≤ ∑ k ∈ Finset.univ.erase i, L k j * G.d k x y :=
  (hL.2 hx hy j).trans_eq (erase_input (vec G x y) h).2

theorem row_bound (hL : L ∈ lip G f U) (hr : Row L i j) (hx : x ∈ U) (hy : y ∈ U) :
    G.d j (f.func x) (f.func y) ≤ L i j * G.d i x y := by
  apply (hL.2 hx hy j).trans_eq
  exact Finset.sum_eq_single i (fun k _ hk => by rw [hr k hk, zero_mul]) (by simp)

theorem column_contribution (_hL : L ∈ lip G f U) (hc : Col L i j)
    (_hx : x ∈ U) (_hy : y ∈ U) (k : I) (hk : k ≠ j) :
    L i k * G.d i x y = 0 := by rw [hc k hk, zero_mul]

theorem diagonal_upper (hL : L ∈ lip G f U) (hd : Diagonal L) (j : I)
    (hx : x ∈ U) (hy : y ∈ U) : G.d j (f.func x) (f.func y) ≤ L j j * G.d j x y :=
  row_bound hL (fun k hk => hd k j hk) hx hy

theorem two_sided (hL : L ∈ lip G f U) (hK : K ∈ coLip G f U) (hr : Row L j j)
    (hx : x ∈ U) (hy : y ∈ U) :
    K j j * G.d j x y ≤ G.d j (f.func x) (f.func y) ∧
    G.d j (f.func x) (f.func y) ≤ L j j * G.d j x y :=
  ⟨co_term hK hx hy j j, row_bound hL hr hx hy⟩

theorem diagonal_bounds (hL : L ∈ lip G f U) (hK : K ∈ coLip G f U) (hd : Diagonal L) :
    ∀ j ⦃x y⦄, x ∈ U → y ∈ U →
      K j j * G.d j x y ≤ G.d j (f.func x) (f.func y) ∧
      G.d j (f.func x) (f.func y) ≤ L j j * G.d j x y :=
  fun j {_ _} hx hy => two_sided hL hK (fun k hk => hd k j hk) hx hy

theorem finite_diagonal (hL : L ∈ lip G f U) (hK : K ∈ coLip G f U) (hd : Diagonal L)
    (hfL : ∀ j, L j j < ⊤) (hfK : ∀ j, K j j < ⊤) :
    ∃ l k : I → ℝ≥0, (∀ j, ↑(l j) = L j j ∧ ↑(k j) = K j j) ∧
      ∀ j ⦃x y⦄, x ∈ U → y ∈ U →
        ↑(k j) * G.d j x y ≤ G.d j (f.func x) (f.func y) ∧
        G.d j (f.func x) (f.func y) ≤ ↑(l j) * G.d j x y := by
  refine ⟨fun j => (L j j).toNNReal, fun j => (K j j).toNNReal, ?_, ?_⟩
  · exact fun j => ⟨ENNReal.coe_toNNReal (hfL j).ne, ENNReal.coe_toNNReal (hfK j).ne⟩
  · intro j x y hx hy
    simpa [ENNReal.coe_toNNReal, (hfL j).ne, (hfK j).ne] using diagonal_bounds hL hK hd j hx hy

theorem positive_channel (hK : K ∈ coLip G f U) (hk : 0 < K i j)
    (hx : x ∈ U) (hy : y ∈ U) (h : 0 < G.d i x y) : 0 < G.d j (f.func x) (f.func y) :=
  (ENNReal.mul_pos hk.ne' h.ne').trans_le (co_term hK hx hy i j)

theorem reflect_zero (hK : K ∈ coLip G f U) (hk : ∀ j, 0 < K j j) (hx : x ∈ U) (hy : y ∈ U)
    (h : GaugeZeroRelated G.d (f.func x) (f.func y)) : GaugeZeroRelated G.d x y := by
  intro j
  by_contra hn
  exact (positive_channel hK (hk j) hx hy (pos_iff_ne_zero.mpr hn)).ne' (h j)

end
end HCH02
