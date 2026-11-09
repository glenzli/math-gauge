import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Basic

/- Based on the frozen chapter of The Operator Evolution Theory,
   Zhe Li / Glen Li / glenzli, https://glenzli.com/books/oet/, CC BY 4.0.
   This file is a new Lean formalization of that historical text. -/
noncomputable section
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
open formal_oet.vol_01.ch_01_foundations

namespace HCH02

abbrev Mat (I : Type) := I → I → ENNReal

variable {X I : Type} [Fintype I] {bot : X}

def display (M : Mat I) : Matrix I I ENNReal := fun j i => M i j

theorem display_injective : Function.Injective (display : Mat I → Matrix I I ENNReal) := by
  intro A B h
  funext i j
  exact congrFun (congrFun h j) i

def mmul (B A : Mat I) : Mat I := fun i j => ∑ k, B k j * A i k

theorem display_mmul (B A : Mat I) : display (mmul B A) = display B * display A := rfl

def eye : Mat I := fun i j => if i = j then 1 else 0

theorem display_eye : display (eye : Mat I) = 1 := by
  ext j i
  simp [display, eye, Matrix.one_apply, eq_comm]

def act (M : Mat I) (v : I → ENNReal) (j : I) : ENNReal := ∑ i, M i j * v i

@[simp] theorem act_eye (v : I → ENNReal) (j : I) : act eye v j = v j := by
  classical
  simp [act, eye]

@[simp] theorem mmul_eye (A : Mat I) : mmul A eye = A := by
  classical
  funext i j
  simp [mmul, eye]

@[simp] theorem eye_mmul (A : Mat I) : mmul eye A = A := by
  classical
  funext i j
  simp [mmul, eye]

theorem act_mmul (B A : Mat I) (v : I → ENNReal) (j : I) :
    act (mmul B A) v j = act B (fun k => act A v k) j := by
  simp only [act, mmul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

def product : List (Mat I) → Mat I
  | [] => eye
  | A :: As => mmul (product As) A

@[simp] theorem product_nil : product ([] : List (Mat I)) = eye := rfl
@[simp] theorem product_cons (A : Mat I) (As : List (Mat I)) :
    product (A :: As) = mmul (product As) A := rfl
@[simp] theorem product_singleton (A : Mat I) : product [A] = A := eye_mmul A

theorem display_product (As : List (Mat I)) :
    display (product As) = (As.map display).reverse.prod := by
  induction As with
  | nil => simpa using (display_eye (I := I))
  | cons A As ih => simp [display_mmul, ih]

def ident : Operator X bot := ⟨id, rfl⟩

def comp (ψ φ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ φ.func, by simp [φ.preserves_bot, ψ.preserves_bot]⟩

theorem dom_comp (ψ φ : Operator X bot) :
    dom (comp ψ φ) = {x | x ∈ dom φ ∧ φ.func x ∈ dom ψ} := by
  ext x
  change ψ.func (φ.func x) ≠ bot ↔ φ.func x ≠ bot ∧ ψ.func (φ.func x) ≠ bot
  constructor
  · intro h
    refine ⟨?_, h⟩
    intro hx
    exact h (by rw [hx, ψ.preserves_bot])
  · exact And.right

def Lip (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {L | U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    d j (φ.func x) (φ.func y) ≤ act L (fun i => d i x y) j}

def GlobalLip (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  Lip d φ (dom φ)

def CoLip (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) : Set (Mat I) :=
  {K | U.Nonempty ∧ U ⊆ dom φ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j,
    act K (fun i => d i x y) j ≤ d j (φ.func x) (φ.func y)}

variable {d : I → X → X → ENNReal} {φ ψ : Operator X bot}
  {U V : Set X} {L K : Mat I} {x y : X} {i j : I}

theorem mem_globalLip_iff : L ∈ GlobalLip d φ ↔
    ∀ x ∈ dom φ, ∀ y ∈ dom φ, ∀ j,
      d j (φ.func x) (φ.func y) ≤ ∑ i, L i j * d i x y :=
  ⟨fun h => h.2, fun h => ⟨Set.Subset.rfl, h⟩⟩

theorem lip_restrict (h : L ∈ Lip d φ V) (hUV : U ⊆ V) : L ∈ Lip d φ U :=
  ⟨hUV.trans h.1, fun x hx y hy j => h.2 x (hUV hx) y (hUV hy) j⟩

theorem global_restrict (hU : U ⊆ dom φ) : GlobalLip d φ ⊆ Lip d φ U :=
  fun _ h => lip_restrict h hU

theorem lip_family_antitone (hUV : U ⊆ V) : Lip d φ V ⊆ Lip d φ U :=
  fun _ h => lip_restrict h hUV

def entryInf (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (i j : I) : ENNReal := sInf ((fun M : Mat I => M i j) '' Lip d φ U)

theorem entryInf_mono (hUV : U ⊆ V) : entryInf d φ U i j ≤ entryInf d φ V i j := by
  apply sInf_le_sInf
  exact Set.image_mono (lip_family_antitone hUV)

theorem lip_singleton [Unique I] (h : L ∈ Lip d φ U) (hx : x ∈ U) (hy : y ∈ U) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  simpa [act, Subsingleton.elim (default : I) i] using h.2 x hx y hy i

theorem lip_one_component (hi : ∀ k : I, k = i) (h : L ∈ Lip d φ U)
    (hx : x ∈ U) (hy : y ∈ U) :
    d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  have he : act L (fun k => d k x y) i = L i i * d i x y := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      exact (hki (hi k)).elim
    · simp
  exact he ▸ h.2 x hx y hy i

theorem lip_comp {A B : Mat I} (hU : U ⊆ dom (comp ψ φ))
    (hA : A ∈ Lip d φ U) (hB : B ∈ Lip d ψ (φ.func '' U)) :
    mmul B A ∈ Lip d (comp ψ φ) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  change d j (ψ.func (φ.func x)) (ψ.func (φ.func y)) ≤ _
  rw [act_mmul]
  apply (hB.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j).trans
  exact Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2 x hx y hy k) (B k j)

theorem colip_comp {A B : Mat I} (hU : U ⊆ dom (comp ψ φ))
    (hA : A ∈ CoLip d φ U) (hB : B ∈ CoLip d ψ (φ.func '' U)) :
    mmul B A ∈ CoLip d (comp ψ φ) U := by
  refine ⟨hA.1, hU, ?_⟩
  intro x hx y hy j
  rw [act_mmul]
  apply le_trans _ (hB.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)
  exact Finset.sum_le_sum fun k _ => mul_le_mul_right (hA.2.2 x hx y hy k) (B k j)

theorem colip_term (h : K ∈ CoLip d φ U) (hx : x ∈ U) (hy : y ∈ U) :
    K i j * d i x y ≤ d j (φ.func x) (φ.func y) :=
  (Finset.single_le_sum (fun k _ => zero_le (K k j * d k x y)) (Finset.mem_univ i)).trans
    (h.2.2 x hx y hy j)

theorem colip_zero (h : K ∈ CoLip d φ (dom φ)) (hx : x ∈ dom φ) (hy : y ∈ dom φ)
    (hout : d j (φ.func x) (φ.func y) = 0) (hin : 0 < d i x y) : K i j = 0 := by
  have hz : K i j * d i x y = 0 := le_antisymm (hout ▸ colip_term h hx hy) (zero_le _)
  exact (mul_eq_zero.mp hz).resolve_right (ne_of_gt hin)

theorem lip_ident (hU : U ⊆ dom (ident : Operator X bot)) :
    eye ∈ Lip d (ident : Operator X bot) U := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  simp [ident]

theorem colip_ident (hne : U.Nonempty) (hU : U ⊆ dom (ident : Operator X bot)) :
    eye ∈ CoLip d (ident : Operator X bot) U := by
  refine ⟨hne, hU, ?_⟩
  intro x hx y hy j
  simp [ident]

def Channel (I : Type) := I × I
def Row (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ i → L k j = 0
def Col (L : Mat I) (i j : I) : Prop := ∀ k, k ≠ j → L i k = 0
def Diagonal (L : Mat I) : Prop := ∀ i j, i ≠ j → L i j = 0
def RowDecoupled (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (j : I) :
    Prop := ∃ L ∈ Lip d φ U, ∃ i, Row L i j
def ColDecoupled (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (i : I) :
    Prop := ∃ L ∈ Lip d φ U, ∃ j, Col L i j

theorem zero_term (h : L i j = 0) : L i j * d i x y = 0 := by rw [h, zero_mul]

theorem erase_zero_term (h : L i j = 0) :
    act L (fun k => d k x y) j = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  classical
  simpa [h, act] using (Finset.sum_erase_add (s := Finset.univ)
    (f := fun k => L k j * d k x y) (Finset.mem_univ i)).symm

theorem row_sum (h : Row L i j) (v : I → ENNReal) : act L v j = L i j * v i := by
  classical
  apply Finset.sum_eq_single i
  · intro k hk hki
    rw [h k hki, zero_mul]
  · simp

theorem row_bound (hL : L ∈ Lip d φ U) (h : Row L i j) (hx : x ∈ U) (hy : y ∈ U) :
    d j (φ.func x) (φ.func y) ≤ L i j * d i x y := by
  simpa [row_sum h] using hL.2 x hx y hy j

theorem col_contribution (h : Col L i j) {k : I} (hk : k ≠ j) :
    L i k * d i x y = 0 := zero_term (h k hk)

theorem diagonal_bound (hL : L ∈ Lip d φ U) (h : Diagonal L)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  row_bound hL (fun k hk => h k j hk) hx hy

theorem scalar_sandwich (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    (h : Row L j j) (hx : x ∈ U) (hy : y ∈ U) :
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  ⟨colip_term hK hx hy, row_bound hL h hx hy⟩

theorem diagonal_sandwich (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    (h : Diagonal L) : ∀ j, ∀ x ∈ U, ∀ y ∈ U,
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j _ hx _ hy => scalar_sandwich hL hK (fun k hk => h k j hk) hx hy

theorem finite_diagonal_sandwich (hL : L ∈ Lip d φ U) (hK : K ∈ CoLip d φ U)
    (h : Diagonal L) (hf : ∀ j, L j j < ⊤ ∧ K j j < ⊤) : ∀ j,
    L j j < ⊤ ∧ K j j < ⊤ ∧ ∀ x ∈ U, ∀ y ∈ U,
    K j j * d j x y ≤ d j (φ.func x) (φ.func y) ∧
    d j (φ.func x) (φ.func y) ≤ L j j * d j x y :=
  fun j => ⟨(hf j).1, (hf j).2, diagonal_sandwich hL hK h j⟩

theorem positive_channel (hK : K ∈ CoLip d φ U) (h : 0 < K i j)
    (hx : x ∈ U) (hy : y ∈ U) (hxy : 0 < d i x y) :
    0 < d j (φ.func x) (φ.func y) := by
  have hp : 0 < K i j * d i x y := by positivity
  exact hp.trans_le (colip_term hK hx hy)

theorem reflects_zero (hK : K ∈ CoLip d φ U) (h : ∀ j, 0 < K j j)
    (hx : x ∈ U) (hy : y ∈ U) (hout : GaugeZeroRelated d (φ.func x) (φ.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra hn
  have hp := positive_channel hK (h j) hx hy (pos_iff_ne_zero.mpr hn)
  rw [hout j] at hp
  exact (lt_irrefl 0) hp

theorem perturb_forward (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ d j (φ.func x) (φ.func y) + δ j + δ j := by
  calc
    _ ≤ d j (ψ.func x) (φ.func x) +
        (d j (φ.func x) (φ.func y) + d j (φ.func y) (ψ.func y)) :=
      ((hd j).triangle _ _ _).trans (add_le_add le_rfl ((hd j).triangle _ _ _))
    _ ≤ δ j + (d j (φ.func x) (φ.func y) + δ j) := by
      apply add_le_add
      · rw [(hd j).symm]
        exact hδ x hx j
      · exact add_le_add le_rfl (hδ y hy j)
    _ = _ := by simp only [add_comm]

theorem perturb_reverse (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (φ.func x) (φ.func y) ≤ d j (ψ.func x) (ψ.func y) + δ j + δ j := by
  apply perturb_forward hd (φ := ψ) (ψ := φ) _ hx hy j
  intro z hz j
  rw [(hd j).symm]
  exact hδ z hz j

theorem perturb_lip (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hL : L ∈ Lip d φ U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ψ.func x) (ψ.func y) ≤ act L (fun i => d i x y) j + 2 * δ j := by
  calc
    _ ≤ d j (φ.func x) (φ.func y) + δ j + δ j := perturb_forward hd hδ hx hy j
    _ ≤ act L (fun i => d i x y) j + δ j + δ j :=
      add_le_add (add_le_add (hL.2 x hx y hy j) le_rfl) le_rfl
    _ = _ := by rw [two_mul, add_assoc]

theorem perturb_colip (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
    {δ : I → ENNReal} (hδ : ∀ z ∈ U, ∀ j, d j (φ.func z) (ψ.func z) ≤ δ j)
    (hK : K ∈ CoLip d φ U) (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    act K (fun i => d i x y) j ≤ d j (ψ.func x) (ψ.func y) + 2 * δ j := by
  simpa only [two_mul, add_assoc] using (hK.2.2 x hx y hy j).trans
    (perturb_reverse hd hδ hx hy j)

end HCH02
