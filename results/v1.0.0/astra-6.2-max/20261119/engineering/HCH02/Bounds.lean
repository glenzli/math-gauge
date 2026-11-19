import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/- The Operator Evolution Theory, Zhe Li (Glen Li / glenzli).
   Chapter 2, frozen text 2d2f76c8392daf62. Adapted to Lean under CC BY 4.0. -/
namespace HCH02

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal Classical
noncomputable section

variable {X I : Type} {b : X}

structure Gauge (X I : Type) (b : X) [Fintype I] [Nonempty I] where
  d : I → X → X → ℝ≥0∞
  metric : ∀ i, ExtendedPseudoMetric X b (d i)

abbrev Coeff (I : Type) := I → I → ℝ≥0∞

def display (A : Coeff I) : Matrix I I ℝ≥0∞ := fun j i => A i j

theorem display_entry (A : Coeff I) (i j : I) : display A j i = A i j := rfl

variable [Fintype I]

def mul (B A : Coeff I) (i j : I) := ∑ k, B k j * A i k
def act (A : Coeff I) (v : I → ℝ≥0∞) (j : I) := ∑ i, A i j * v i

theorem display_mul (B A : Coeff I) : display (mul B A) = display B * display A := rfl

theorem act_mul (B A : Coeff I) (v : I → ℝ≥0∞) :
    act (mul B A) v = act B (act A v) :=
  (Matrix.mulVec_mulVec v (display B) (display A)).symm

theorem act_mono (A : Coeff I) {v w : I → ℝ≥0∞} (h : v ≤ w) : act A v ≤ act A w :=
  fun j => Finset.sum_le_sum fun i _ => mul_le_mul_right (h i) (A i j)

theorem term_le_act (A : Coeff I) (v : I → ℝ≥0∞) (i j : I) :
    A i j * v i ≤ act A v j :=
  Finset.single_le_sum (f := fun k => A k j * v k) (fun _ _ => zero_le _) (Finset.mem_univ i)

theorem top_entry {A : Coeff I} {i j : I} (h : A i j = ⊤) (v : I → ℝ≥0∞) :
    (v i = 0 → A i j * v i = 0) ∧
    (0 < v i → A i j * v i = ⊤ ∧ act A v j = ⊤) := by
  refine ⟨fun hz => by rw [hz, mul_zero], fun hp => ?_⟩
  have he : A i j * v i = ⊤ := by rw [h, ENNReal.top_mul hp.ne']
  exact ⟨he, top_unique (he ▸ term_le_act A v i j)⟩

def unitM (I : Type) : Coeff I := fun i j => if i = j then 1 else 0

omit [Fintype I] in
theorem display_unit : display (unitM I) = (1 : Matrix I I ℝ≥0∞) := by
  ext j i
  simp [display, unitM, Matrix.one_apply, eq_comm]

@[simp] theorem act_unit (v : I → ℝ≥0∞) : act (unitM I) v = v := by
  funext j
  simp [act, unitM, ite_mul]

@[simp] theorem mul_unit (A : Coeff I) : mul A (unitM I) = A := by
  funext i j
  simp [mul, unitM, mul_ite]

def ident (b : X) : Operator X b := ⟨id, rfl⟩
def comp (g f : Operator X b) : Operator X b :=
  ⟨g.func ∘ f.func, by simp [f.preserves_bot, g.preserves_bot]⟩

variable {f g : Operator X b} {U V : Set X}

theorem comp_domain : U ⊆ dom (comp g f) ↔ U ⊆ dom f ∧ f.func '' U ⊆ dom g := by
  constructor
  · intro h
    refine ⟨fun x hx he => h hx ?_, ?_⟩
    · change g.func (f.func x) = b
      rw [he, g.preserves_bot]
    · rintro _ ⟨x, hx, rfl⟩
      exact h hx
  · rintro ⟨_, h⟩ x hx
    exact h ⟨x, hx, rfl⟩

variable [Nonempty I] (G : Gauge X I b)

def vec (x y : X) (i : I) := G.d i x y

def lip (f : Operator X b) (U : Set X) : Set (Coeff I) :=
  {A | U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    vec G (f.func x) (f.func y) ≤ act A (vec G x y)}

def globalLip (f : Operator X b) := lip G f (dom f)

def coLip (f : Operator X b) (U : Set X) : Set (Coeff I) :=
  {A | U.Nonempty ∧ U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U →
    act A (vec G x y) ≤ vec G (f.func x) (f.func y)}

variable {G} {A B : Coeff I} {x y : X} {i j : I}

theorem lip_iff : A ∈ lip G f U ↔ U ⊆ dom f ∧ ∀ ⦃x y⦄, x ∈ U → y ∈ U → ∀ j,
    G.d j (f.func x) (f.func y) ≤ ∑ i, A i j * G.d i x y := Iff.rfl

theorem coLip_iff : A ∈ coLip G f U ↔ U.Nonempty ∧ U ⊆ dom f ∧
    ∀ ⦃x y⦄, x ∈ U → y ∈ U → ∀ j,
      (∑ i, A i j * G.d i x y) ≤ G.d j (f.func x) (f.func y) := Iff.rfl

theorem singleton_lip [Subsingleton I] (i : I) :
    A ∈ globalLip G f ↔ ∀ ⦃x y⦄, x ∈ dom f → y ∈ dom f →
      G.d i (f.func x) (f.func y) ≤ A i i * G.d i x y := by
  have e (x y : X) : act A (vec G x y) i = A i i * G.d i x y :=
    Fintype.sum_subsingleton _ i
  constructor
  · intro h x y hx hy
    exact (h.2 hx hy i).trans_eq (e x y)
  · intro h
    refine ⟨Set.Subset.rfl, fun {x y} hx hy j => ?_⟩
    obtain rfl := Subsingleton.elim j i
    exact (h hx hy).trans_eq (e x y).symm

theorem lip_shrink (h : U ⊆ V) : lip G f V ⊆ lip G f U :=
  fun _ hA => ⟨h.trans hA.1, fun {_ _} hx hy => hA.2 (h hx) (h hy)⟩

theorem global_restrict (h : U ⊆ dom f) : globalLip G f ⊆ lip G f U := lip_shrink h

def entryInf (G : Gauge X I b) (f : Operator X b) (U : Set X) (i j : I) :=
  sInf ((fun A : Coeff I => A i j) '' lip G f U)

theorem entryInf_mono (h : U ⊆ V) : entryInf G f U i j ≤ entryInf G f V i j :=
  sInf_le_sInf (Set.image_mono (lip_shrink h))

theorem lip_comp (h : U ⊆ dom (comp g f)) (hA : A ∈ lip G f U)
    (hB : B ∈ lip G g (f.func '' U)) : mul B A ∈ lip G (comp g f) U := by
  refine ⟨h, fun {x y} hx hy => ?_⟩
  rw [act_mul]
  exact (hB.2 ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩).trans (act_mono B (hA.2 hx hy))

theorem co_comp (h : U ⊆ dom (comp g f)) (hA : A ∈ coLip G f U)
    (hB : B ∈ coLip G g (f.func '' U)) : mul B A ∈ coLip G (comp g f) U := by
  refine ⟨hA.1, h, fun {x y} hx hy => ?_⟩
  rw [act_mul]
  exact (act_mono B (hA.2.2 hx hy)).trans (hB.2.2 ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩)

theorem co_term (hA : A ∈ coLip G f U) (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    A i j * G.d i x y ≤ G.d j (f.func x) (f.func y) :=
  (term_le_act A (vec G x y) i j).trans (hA.2.2 hx hy j)

theorem collapsed_entry (hA : A ∈ coLip G f (dom f)) (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hout : G.d j (f.func x) (f.func y) = 0) (hin : 0 < G.d i x y) : A i j = 0 := by
  have h := co_term hA hx hy i j
  rw [hout, nonpos_iff_eq_zero, mul_eq_zero] at h
  exact h.resolve_right hin.ne'

def CloseOn (G : Gauge X I b) (f g : Operator X b) (U : Set X) (δ : I → ℝ≥0∞) :=
  ∀ z ∈ U, ∀ j, G.d j (f.func z) (g.func z) ≤ δ j

variable {δ : I → ℝ≥0∞}

theorem close_swap (h : CloseOn G f g U δ) : CloseOn G g f U δ := by
  intro z hz j
  rw [(G.metric j).symm]
  exact h z hz j

theorem perturb (_hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    G.d j (g.func x) (g.func y) ≤ G.d j (f.func x) (f.func y) + δ j + δ j := by
  have t := (G.metric j).triangle
  calc
    _ ≤ G.d j (g.func x) (f.func x) + G.d j (f.func x) (g.func y) := t _ _ _
    _ ≤ δ j + (G.d j (f.func x) (f.func y) + δ j) :=
      add_le_add (close_swap h x hx j) ((t _ (f.func y) _).trans (add_le_add le_rfl (h y hy j)))
    _ = _ := by rw [← add_assoc, add_comm (δ j) (G.d j (f.func x) (f.func y))]

theorem perturb_rev (hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    G.d j (f.func x) (f.func y) ≤ G.d j (g.func x) (g.func y) + δ j + δ j :=
  perturb (by rwa [Set.inter_comm]) (close_swap h) hx hy j

theorem lip_bridge (hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hA : A ∈ lip G f U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    G.d j (g.func x) (g.func y) ≤ act A (vec G x y) j + 2 * δ j := by
  rw [two_mul, ← add_assoc]
  exact (perturb hU h hx hy j).trans (add_le_add (add_le_add (hA.2 hx hy j) le_rfl) le_rfl)

theorem co_bridge (hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hA : A ∈ coLip G f U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    act A (vec G x y) j ≤ G.d j (g.func x) (g.func y) + 2 * δ j := by
  rw [two_mul, ← add_assoc]
  exact (hA.2.2 hx hy j).trans (perturb_rev hU h hx hy j)

theorem lip_bridge_rev (hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hA : A ∈ lip G g U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    G.d j (f.func x) (f.func y) ≤ act A (vec G x y) j + 2 * δ j :=
  lip_bridge (by rwa [Set.inter_comm]) (close_swap h) hA hx hy j

theorem co_bridge_rev (hU : U ⊆ dom f ∩ dom g) (h : CloseOn G f g U δ)
    (hA : A ∈ coLip G g U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    act A (vec G x y) j ≤ G.d j (f.func x) (f.func y) + 2 * δ j :=
  co_bridge (by rwa [Set.inter_comm]) (close_swap h) hA hx hy j

end
end HCH02
