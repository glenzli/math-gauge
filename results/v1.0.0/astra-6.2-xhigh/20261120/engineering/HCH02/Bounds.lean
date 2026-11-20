import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/- Formalization of chapter 2 of The Operator Evolution Theory, Zhe Li
(Glen Li / glenzli), https://glenzli.com/books/oet/, CC BY 4.0.
Historical text 2d2f76c8392daf62. -/
open formal_oet.vol_01.ch_01_foundations
open scoped BigOperators
noncomputable section
namespace HCH02

abbrev Mat (I : Type) := I → I → ENNReal
variable {I X : Type} {b : X}

def display (A : Mat I) : Matrix I I ENNReal := fun j i => A i j

def mul [Fintype I] (B A : Mat I) : Mat I := fun i j => ∑ k, B k j * A i k

theorem display_mul [Fintype I] (B A : Mat I) :
    display (mul B A) = display B * display A := rfl

structure Gauge (X I : Type) (b : X) [Fintype I] [Nonempty I] where
  d : I → X → X → ENNReal
  metric : ∀ i, ExtendedPseudoMetric X b (d i)

def act [Fintype I] (A : Mat I) (v : I → ENNReal) (j : I) := ∑ i, A i j * v i

theorem act_mul [Fintype I] (B A : Mat I) (v : I → ENNReal) (j : I) :
    act (mul B A) v j = act B (act A v) j := by
  simp only [act, mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem act_mono [Fintype I] (A : Mat I) {v w : I → ENNReal} (h : ∀ i, v i ≤ w i)
    (j : I) : act A v j ≤ act A w j :=
  Finset.sum_le_sum fun i _ => mul_le_mul_right (h i) _

def comp (q p : Operator X b) : Operator X b :=
  ⟨q.func ∘ p.func, by simp [p.preserves_bot, q.preserves_bot]⟩

theorem comp_domain {p q : Operator X b} {U : Set X} :
    U ⊆ dom (comp q p) ↔ U ⊆ dom p ∧ operator_image p U ⊆ dom q := by
  constructor
  · intro h
    constructor
    · intro x hx he
      exact h hx (by change q.func (p.func x) = b; rw [he, q.preserves_bot])
    · rintro _ ⟨x, hx, rfl⟩
      exact h hx
  · exact fun h x hx => h.2 ⟨x, hx, rfl⟩

variable [Fintype I] [Nonempty I]
variable (g : Gauge X I b)

def vec (x y : X) : I → ENNReal := fun i => g.d i x y

def lip (p : Operator X b) (U : Set X) : Set (Mat I) :=
  {A | U ⊆ dom p ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    g.d j (p.func x) (p.func y) ≤ act A (vec g x y) j}

def globalLip (p : Operator X b) := lip g p (dom p)

open scoped Classical in
theorem infinite_term (v : ENNReal) : ⊤ * v = if v = 0 then 0 else ⊤ := ENNReal.top_mul'

def coLip (p : Operator X b) (U : Set X) : Set (Mat I) :=
  {A | U.Nonempty ∧ U ⊆ dom p ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    act A (vec g x y) j ≤ g.d j (p.func x) (p.func y)}

variable {g} {p q : Operator X b} {U V : Set X} {A B : Mat I} {x y : X} {i j : I}

theorem singleton_lip [Subsingleton I] :
    A ∈ globalLip g p ↔ ∀ x ∈ dom p, ∀ y ∈ dom p,
      g.d i (p.func x) (p.func y) ≤ A i i * g.d i x y := by
  have hs (v : I → ENNReal) : act A v i = A i i * v i := by
    exact Fintype.sum_subsingleton _ i
  constructor
  · intro h x hx y hy
    simpa only [hs, vec] using h.2 x hx y hy i
  · refine fun h => ⟨fun _ hx => hx, fun x hx y hy k => ?_⟩
    cases Subsingleton.elim k i
    simpa only [hs, vec] using h x hx y hy

theorem restrict_lip (h : U ⊆ V) : lip g p V ⊆ lip g p U :=
  fun _ hA => ⟨h.trans hA.1, fun x hx y hy => hA.2 x (h hx) y (h hy)⟩

theorem restrict_global (h : U ⊆ dom p) : globalLip g p ⊆ lip g p U := restrict_lip h

def entryInf (g : Gauge X I b) (p : Operator X b) (U : Set X) (i j : I) : ENNReal :=
  sInf ((fun A : Mat I => A i j) '' lip g p U)

theorem entryInf_le (h : U ⊆ V) : entryInf g p U i j ≤ entryInf g p V i j :=
  sInf_le_sInf (Set.image_mono (restrict_lip h))

theorem lip_comp (h : U ⊆ dom (comp q p)) (hA : A ∈ lip g p U)
    (hB : B ∈ lip g q (operator_image p U)) : mul B A ∈ lip g (comp q p) U := by
  refine ⟨h, fun x hx y hy j => ?_⟩
  rw [act_mul]
  exact (hB.2 _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ j).trans (act_mono B (hA.2 x hx y hy) j)

theorem co_comp (h : U ⊆ dom (comp q p)) (hA : A ∈ coLip g p U)
    (hB : B ∈ coLip g q (operator_image p U)) : mul B A ∈ coLip g (comp q p) U := by
  refine ⟨hA.1, h, fun x hx y hy j => ?_⟩
  rw [act_mul]
  exact (act_mono B (hA.2.2 x hx y hy) j).trans (hB.2.2 _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ j)

theorem co_term (h : A ∈ coLip g p U) (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    A i j * g.d i x y ≤ g.d j (p.func x) (p.func y) :=
  (Finset.single_le_sum (f := fun k => A k j * g.d k x y)
    (fun _ _ => zero_le _) (Finset.mem_univ i)).trans (h.2.2 x hx y hy j)

theorem co_degenerate (h : A ∈ coLip g p (dom p)) (hx : x ∈ dom p) (hy : y ∈ dom p)
    (hz : g.d j (p.func x) (p.func y) = 0) (hp : 0 < g.d i x y) : A i j = 0 := by
  have ht := co_term h hx hy i j
  rw [hz] at ht
  have he : A i j * g.d i x y = 0 := le_antisymm ht (zero_le _)
  exact (mul_eq_zero.mp he).resolve_right hp.ne'

def CloseOn (g : Gauge X I b) (p q : Operator X b) (U : Set X) (δ : I → ENNReal) :=
  U ⊆ dom p ∩ dom q ∧ ∀ z ∈ U, ∀ j, g.d j (p.func z) (q.func z) ≤ δ j

variable {δ : I → ENNReal}

theorem close_swap (h : CloseOn g p q U δ) : CloseOn g q p U δ :=
  ⟨fun _ hz => (h.1 hz).symm, fun z hz j => (g.metric j).symm _ _ ▸ h.2 z hz j⟩

theorem perturb (h : CloseOn g p q U δ) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    g.d j (q.func x) (q.func y) ≤ g.d j (p.func x) (p.func y) + δ j + δ j := by
  calc
    _ ≤ g.d j (q.func x) (p.func x) + g.d j (p.func x) (q.func y) :=
      (g.metric j).triangle _ _ _
    _ ≤ δ j + (g.d j (p.func x) (p.func y) + δ j) :=
      add_le_add ((close_swap h).2 x hx j)
        (((g.metric j).triangle _ (p.func y) _).trans (add_le_add le_rfl (h.2 y hy j)))
    _ = _ := by rw [← add_assoc, add_comm (δ j) (g.d j _ _)]

theorem perturb_rev (h : CloseOn g p q U δ) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    g.d j (p.func x) (p.func y) ≤ g.d j (q.func x) (q.func y) + δ j + δ j :=
  perturb (close_swap h) hx hy j

theorem perturb_lip (h : CloseOn g p q U δ) (hA : A ∈ lip g p U)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    g.d j (q.func x) (q.func y) ≤ act A (vec g x y) j + δ j + δ j :=
  (perturb h hx hy j).trans (add_le_add (add_le_add (hA.2 x hx y hy j) le_rfl) le_rfl)

theorem perturb_co (h : CloseOn g p q U δ) (hA : A ∈ coLip g p U)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    act A (vec g x y) j ≤ g.d j (q.func x) (q.func y) + δ j + δ j :=
  (hA.2.2 x hx y hy j).trans (perturb_rev h hx hy j)

end HCH02
