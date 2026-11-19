import formal_oet.vol_01.ch_01_foundations.operator_space
import Mathlib.Data.Matrix.Mul

/-! Chapter 2 of Zhe Li (Glen Li / glenzli), The Operator Evolution Theory.
Historical snapshot, adapted into Lean. https://glenzli.com/books/oet/
ORCID 0009-0006-6536-3453. CC BY 4.0. -/

open scoped BigOperators ENNReal
open formal_oet.vol_01.ch_01_foundations

namespace HCH02

noncomputable section

variable {X I : Type} {bot : X} {d : I → X → X → ℝ≥0∞}
variable {p q : Operator X bot} {U V : Set X}

abbrev Coeff (I : Type) := I → I → ℝ≥0∞

def display (M : Coeff I) : Matrix I I ℝ≥0∞ := Matrix.of fun j i => M i j

theorem display_apply (M : Coeff I) (i j : I) : display M j i = M i j := rfl

def unit : Coeff I := by
  classical
  exact fun i j => if i = j then 1 else 0

theorem unit_apply [DecidableEq I] (i j : I) :
    unit i j = if i = j then 1 else 0 := by
  by_cases h : i = j <;> simp [unit, h]

variable [Fintype I]

def mul (A B : Coeff I) : Coeff I := fun i j => ∑ k, A k j * B i k

theorem display_mul (A B : Coeff I) : display (mul A B) = display A * display B := by
  ext j i
  rw [Matrix.mul_apply]
  rfl

def act (M : Coeff I) (v : I → ℝ≥0∞) (j : I) : ℝ≥0∞ := ∑ i, M i j * v i

theorem act_mono (M : Coeff I) {v w : I → ℝ≥0∞} (h : ∀ i, v i ≤ w i) (j : I) :
    act M v j ≤ act M w j :=
  Finset.sum_le_sum fun i _ => mul_le_mul_right (h i) _

theorem act_mul (A B : Coeff I) (v : I → ℝ≥0∞) (j : I) :
    act (mul A B) v j = act A (act B v) j := by
  simp only [act, mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

theorem act_top (M : Coeff I) (v : I → ℝ≥0∞) (i j : I) (h : M i j = ⊤) :
    (v i = 0 → M i j * v i = 0) ∧ (0 < v i → act M v j = ⊤) := by
  refine ⟨fun hz => by simp [hz], fun hp => top_unique ?_⟩
  simpa only [h, ENNReal.top_mul hp.ne'] using
    (Finset.single_le_sum (f := fun k => M k j * v k) (fun _ _ => zero_le _) (Finset.mem_univ i))

@[simp] theorem unit_mul (M : Coeff I) : mul unit M = M := by
  classical
  funext i j
  simp [mul, unit_apply]

@[simp] theorem mul_unit (M : Coeff I) : mul M unit = M := by
  classical
  funext i j
  simp [mul, unit_apply]

@[simp] theorem act_unit (v : I → ℝ≥0∞) (j : I) : act unit v j = v j := by
  classical
  simp [act, unit_apply]

def product : List (Coeff I) → Coeff I
  | [] => unit
  | M :: Ms => mul (product Ms) M

@[simp] theorem product_nil : product ([] : List (Coeff I)) = unit := rfl

theorem product_cons (M : Coeff I) (Ms : List (Coeff I)) :
    product (M :: Ms) = mul (product Ms) M := rfl

@[simp] theorem product_single (M : Coeff I) : product [M] = M := unit_mul M

def lipOn (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) : Set (Coeff I) :=
  {M | U ⊆ dom p ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j, d j (p.func x) (p.func y) ≤ act M (fun i => d i x y) j}

def lip (d : I → X → X → ℝ≥0∞) (p : Operator X bot) : Set (Coeff I) :=
  lipOn d p (dom p)

def coLipOn (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) : Set (Coeff I) :=
  {M | U.Nonempty ∧ U ⊆ dom p ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j, act M (fun i => d i x y) j ≤ d j (p.func x) (p.func y)}

variable {L K : Coeff I}

theorem lip_single [Subsingleton I] (i : I) :
    L ∈ lip d p ↔ ∀ x ∈ dom p, ∀ y ∈ dom p, d i (p.func x) (p.func y) ≤ L i i * d i x y := by
  have sum_one (v : I → ℝ≥0∞) : act L v i = L i i * v i := by
    classical
    exact Finset.sum_eq_single i (fun k _ h => (h (Subsingleton.elim k i)).elim) (by simp)
  constructor
  · intro h x hx y hy
    simpa only [sum_one] using h.2 x hx y hy i
  · intro h
    refine ⟨Set.Subset.rfl, fun x hx y hy j => ?_⟩
    rw [Subsingleton.elim j i, sum_one]
    exact h x hx y hy

theorem lip_shrink (h : U ⊆ V) : lipOn d p V ⊆ lipOn d p U :=
  fun _ hL => ⟨h.trans hL.1, fun x hx y hy j => hL.2 x (h hx) y (h hy) j⟩

theorem lip_restrict (h : U ⊆ dom p) : lip d p ⊆ lipOn d p U := lip_shrink h

def entryInf (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) (i j : I) : ℝ≥0∞ :=
  sInf ((fun M => M i j) '' lipOn d p U)

theorem entryInf_shrink (h : U ⊆ V) (i j : I) : entryInf d p U i j ≤ entryInf d p V i j :=
  sInf_le_sInf (Set.image_mono (lip_shrink h))

def identity : Operator X bot := ⟨id, rfl⟩

def comp (q p : Operator X bot) : Operator X bot :=
  ⟨q.func ∘ p.func, by simp [p.preserves_bot, q.preserves_bot]⟩

theorem comp_domains (h : U ⊆ dom (comp q p)) : U ⊆ dom p ∧ p.func '' U ⊆ dom q := by
  constructor
  · intro x hx hp
    exact h hx (show q.func (p.func x) = bot by rw [hp, q.preserves_bot])
  · rintro _ ⟨x, hx, rfl⟩
    exact h hx

theorem lip_comp {L₁ L₂ : Coeff I} (h : U ⊆ dom (comp q p))
    (hp : L₁ ∈ lipOn d p U) (hq : L₂ ∈ lipOn d q (p.func '' U)) :
    mul L₂ L₁ ∈ lipOn d (comp q p) U := by
  refine ⟨h, fun x hx y hy j => ?_⟩
  rw [act_mul]
  exact (hq.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j).trans
    (act_mono L₂ (hp.2 x hx y hy) j)

theorem coLip_comp {K₁ K₂ : Coeff I} (h : U ⊆ dom (comp q p))
    (hp : K₁ ∈ coLipOn d p U) (hq : K₂ ∈ coLipOn d q (p.func '' U)) :
    mul K₂ K₁ ∈ coLipOn d (comp q p) U := by
  refine ⟨hp.1, h, fun x hx y hy j => ?_⟩
  rw [act_mul]
  exact (act_mono K₂ (hp.2.2 x hx y hy) j).trans
    (hq.2.2 _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ j)

theorem coLip_term (hK : K ∈ coLipOn d p U) {x y : X} (hx : x ∈ U) (hy : y ∈ U) (i j : I) :
    K i j * d i x y ≤ d j (p.func x) (p.func y) :=
  (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)).trans (hK.2.2 x hx y hy j)

theorem coLip_eq_zero (hK : K ∈ coLipOn d p (dom p)) {x y : X}
    (hx : x ∈ dom p) (hy : y ∈ dom p) {i j : I}
    (hout : d j (p.func x) (p.func y) = 0) (hin : 0 < d i x y) : K i j = 0 := by
  have ht := coLip_term hK hx hy i j
  rw [hout, nonpos_iff_eq_zero, mul_eq_zero] at ht
  exact ht.resolve_right hin.ne'

section Perturbation

variable {δ : I → ℝ≥0∞}
variable (hd : ∀ j, ExtendedPseudoMetric X bot (d j))
variable (hδ : ∀ z ∈ U, ∀ j, d j (p.func z) (q.func z) ≤ δ j)
variable {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I)

include hd hδ hx hy

omit [Fintype I] in
theorem perturb_forward (_hU : U ⊆ dom p ∩ dom q) :
    d j (q.func x) (q.func y) ≤ d j (p.func x) (p.func y) + δ j + δ j := by
  calc
    _ ≤ d j (q.func x) (p.func x) + d j (p.func x) (q.func y) := (hd j).triangle _ _ _
    _ ≤ δ j + (d j (p.func x) (p.func y) + δ j) :=
      add_le_add (by rw [(hd j).symm (q.func x)]; exact hδ x hx j)
        (((hd j).triangle (p.func x) (p.func y) (q.func y)).trans (add_le_add le_rfl (hδ y hy j)))
    _ = _ := by rw [add_left_comm, ← add_assoc]

omit [Fintype I] in
theorem perturb_reverse (hU : U ⊆ dom p ∩ dom q) :
    d j (p.func x) (p.func y) ≤ d j (q.func x) (q.func y) + δ j + δ j :=
  perturb_forward hd (fun z hz k => ((hd k).symm _ _).le.trans (hδ z hz k)) hx hy j
    (by simpa only [Set.inter_comm] using hU)

theorem perturb_lip (hU : U ⊆ dom p ∩ dom q) (hL : L ∈ lipOn d p U) :
    d j (q.func x) (q.func y) ≤ act L (fun i => d i x y) j + 2 * δ j := by
  simpa only [two_mul, ← add_assoc] using
    (perturb_forward hd hδ hx hy j hU).trans
      (add_le_add (add_le_add (hL.2 x hx y hy j) le_rfl) le_rfl)

theorem perturb_coLip (hU : U ⊆ dom p ∩ dom q) (hK : K ∈ coLipOn d p U) :
    act K (fun i => d i x y) j ≤ d j (q.func x) (q.func y) + 2 * δ j := by
  simpa only [two_mul, ← add_assoc] using
    (hK.2.2 x hx y hy j).trans (perturb_reverse hd hδ hx hy j hU)

theorem perturb_lip_swap (hU : U ⊆ dom p ∩ dom q) (hL : L ∈ lipOn d q U) :
    d j (p.func x) (p.func y) ≤ act L (fun i => d i x y) j + 2 * δ j := by
  simpa only [two_mul, ← add_assoc] using
    (perturb_reverse hd hδ hx hy j hU).trans
      (add_le_add (add_le_add (hL.2 x hx y hy j) le_rfl) le_rfl)

theorem perturb_coLip_swap (hU : U ⊆ dom p ∩ dom q) (hK : K ∈ coLipOn d q U) :
    act K (fun i => d i x y) j ≤ d j (p.func x) (p.func y) + 2 * δ j := by
  simpa only [two_mul, ← add_assoc] using
    (hK.2.2 x hx y hy j).trans (perturb_forward hd hδ hx hy j hU)

end Perturbation

/-! Lists record the order of application. Index `m` in Lean is step `m+1` in the text. -/

def chain : List (Operator X bot) → Operator X bot
  | [] => identity
  | p :: ps => comp (chain ps) p

def iterImage : List (Operator X bot) → Set X → Set X
  | [], U => U
  | p :: ps, U => iterImage ps (p.func '' U)

theorem iterImage_eq (ps : List (Operator X bot)) (U : Set X) :
    iterImage ps U = (chain ps).func '' U := by
  induction ps generalizing U with
  | nil => exact (Set.image_id U).symm
  | cons p ps ih =>
    change iterImage ps (p.func '' U) = _
    rw [ih, Set.image_image]
    rfl

abbrev Step (X : Type) (bot : X) (I : Type) := Operator X bot × Coeff I

def stepsOfFn {n : Nat} (ps : Fin n → Operator X bot) (Ms : Fin n → Coeff I) :
    List (Step X bot I) :=
  List.ofFn fun m => (ps m, Ms m)

def inputAt (s : List (Step X bot I)) (U : Set X) (m : Nat) : Set X :=
  iterImage ((s.take m).map Prod.fst) U

omit [Fintype I] in
theorem inputAt_succ (s : List (Step X bot I)) (U : Set X) (m : Nat) (hm : m < s.length) :
    inputAt s U (m + 1) = s[m].1.func '' inputAt s U m := by
  induction s generalizing U m with
  | nil => simp at hm
  | cons a s ih =>
    cases m with
    | zero => rfl
    | succ m => exact ih (a.1.func '' U) m (by simpa using hm)

omit [Fintype I] in
theorem inputAt_last (s : List (Step X bot I)) (U : Set X) :
    inputAt s U s.length = (chain (s.map Prod.fst)).func '' U := by
  simp [inputAt, iterImage_eq]

def Stepwise (P : Operator X bot → Set X → Coeff I → Prop)
    (s : List (Step X bot I)) (U : Set X) : Prop :=
  ∀ m (hm : m < s.length), P s[m].1 (inputAt s U m) s[m].2

omit [Fintype I] in
theorem stepwise_ofFn_iff {n : Nat} (P : Operator X bot → Set X → Coeff I → Prop)
    (ps : Fin n → Operator X bot) (Ms : Fin n → Coeff I) (U : Set X) :
    Stepwise P (stepsOfFn ps Ms) U ↔
      ∀ m : Fin n, P (ps m) (inputAt (stepsOfFn ps Ms) U m) (Ms m) := by
  constructor
  · intro h m
    have hm : m.val < (stepsOfFn ps Ms).length := by
      rw [stepsOfFn, List.length_ofFn]
      exact m.isLt
    simpa only [stepsOfFn, List.getElem_ofFn] using h m hm
  · intro h m hm
    have hm' : m < n := by rwa [stepsOfFn, List.length_ofFn] at hm
    simpa only [stepsOfFn, List.getElem_ofFn] using h ⟨m, hm'⟩

omit [Fintype I] in
theorem stepwise_cons (P : Operator X bot → Set X → Coeff I → Prop)
    (a : Step X bot I) (s : List (Step X bot I)) (U : Set X) :
    Stepwise P (a :: s) U ↔ P a.1 U a.2 ∧ Stepwise P s (a.1.func '' U) := by
  constructor
  · intro h
    exact ⟨h 0 (by simp), fun m hm => h (m + 1) (by simpa using hm)⟩
  · rintro ⟨ha, hs⟩ (m | m) hm
    · exact ha
    · exact hs m (by simpa using hm)

omit [Fintype I] in
theorem step_domains (s : List (Step X bot I)) (h : U ⊆ dom (chain (s.map Prod.fst))) :
    Stepwise (fun p V _ => V ⊆ dom p) s U := by
  induction s generalizing U with
  | nil => intro m hm; simp at hm
  | cons a s ih =>
    have hd := comp_domains h
    exact (stepwise_cons ..).2 ⟨hd.1, ih hd.2⟩

theorem lip_unit (h : U ⊆ dom (identity : Operator X bot)) :
    unit ∈ lipOn d (identity (bot := bot)) U :=
  ⟨h, fun x _ y _ j => by simp [identity]⟩

theorem coLip_unit (h : U ⊆ dom (identity : Operator X bot)) (hne : U.Nonempty) :
    unit ∈ coLipOn d (identity (bot := bot)) U :=
  ⟨hne, h, fun x _ y _ j => by simp [identity]⟩

theorem lip_chain (s : List (Step X bot I)) (h : U ⊆ dom (chain (s.map Prod.fst)))
    (hs : Stepwise (fun p V M => M ∈ lipOn d p V) s U) :
    product (s.map Prod.snd) ∈ lipOn d (chain (s.map Prod.fst)) U := by
  induction s generalizing U with
  | nil => exact lip_unit h
  | cons a s ih =>
    obtain ⟨ha, hs⟩ := (stepwise_cons ..).1 hs
    exact lip_comp h ha (ih (comp_domains h).2 hs)

private theorem coLip_chain_aux (s : List (Step X bot I))
    (h : U ⊆ dom (chain (s.map Prod.fst))) (hne : U.Nonempty)
    (hs : Stepwise (fun p V M => M ∈ coLipOn d p V) s U) :
    product (s.map Prod.snd) ∈ coLipOn d (chain (s.map Prod.fst)) U := by
  induction s generalizing U with
  | nil => exact coLip_unit h hne
  | cons a s ih =>
    obtain ⟨ha, hs⟩ := (stepwise_cons ..).1 hs
    exact coLip_comp h ha (ih (comp_domains h).2 (hne.image _) hs)

theorem coLip_chain (s : List (Step X bot I)) (hne : s ≠ [])
    (h : U ⊆ dom (chain (s.map Prod.fst)))
    (hs : Stepwise (fun p V M => M ∈ coLipOn d p V) s U) :
    product (s.map Prod.snd) ∈ coLipOn d (chain (s.map Prod.fst)) U := by
  cases s with
  | nil => exact (hne rfl).elim
  | cons a s => exact coLip_chain_aux _ h ((stepwise_cons ..).1 hs).1.1 hs

/-! For a head matrix and a tail of length `n`, a path specifies all `n` intermediate indices. -/

def pathEntries : (A : Coeff I) → (As : List (Coeff I)) →
    I → I → (Fin As.length → I) → List ℝ≥0∞
  | A, [], i, j, _ => [A i j]
  | A, B :: Bs, i, j, k => A i (k 0) :: pathEntries B Bs (k 0) j (Fin.tail k)

def pathWeight (A : Coeff I) (As : List (Coeff I)) (i j : I) (k : Fin As.length → I) : ℝ≥0∞ :=
  (pathEntries A As i j k).prod

def HasZero (A : Coeff I) (As : List (Coeff I)) (i j : I) (k : Fin As.length → I) : Prop :=
  0 ∈ pathEntries A As i j k

def AllPositive (A : Coeff I) (As : List (Coeff I)) (i j : I) (k : Fin As.length → I) : Prop :=
  ∀ a ∈ pathEntries A As i j k, 0 < a

omit [Fintype I] in
theorem pathEntries_zip (A : Coeff I) (As : List (Coeff I)) (i j : I)
    (k : Fin As.length → I) :
    pathEntries A As i j k = (A :: As).zipWith (fun M e => M e.1 e.2)
      ((i :: List.ofFn k).zip (List.ofFn k ++ [j])) := by
  induction As generalizing A i with
  | nil => simp [pathEntries]
  | cons B Bs ih =>
    have hk : List.ofFn k = k 0 :: List.ofFn (Fin.tail k) := @List.ofFn_succ _ Bs.length k
    rw [hk]
    simp only [pathEntries, List.cons_append, List.zip_cons_cons, List.zipWith_cons_cons]
    exact congrArg (List.cons (A i (k 0))) (ih B (k 0) (Fin.tail k))

omit [Fintype I] in
theorem pathEntries_length (A : Coeff I) (As : List (Coeff I)) (i j : I) (k : Fin As.length → I) :
    (pathEntries A As i j k).length = As.length + 1 := by
  induction As generalizing A i with
  | nil => rfl
  | cons B Bs ih => simp only [pathEntries, List.length_cons, ih]

instance emptyPath : Unique (Fin 0 → I) :=
  ⟨⟨Fin.elim0⟩, fun _ => funext fun m => Fin.elim0 m⟩

omit [Fintype I] in
theorem single_path (A : Coeff I) (i j : I) (k : Fin 0 → I) :
    pathWeight A [] i j k = A i j ∧ (HasZero A [] i j k ↔ A i j = 0) ∧
      (AllPositive A [] i j k ↔ 0 < A i j) := by
  simp [pathWeight, pathEntries, HasZero, AllPositive, eq_comm]

theorem product_expansion (A : Coeff I) (As : List (Coeff I)) (i j : I) :
    product (A :: As) i j = ∑ k : Fin As.length → I, pathWeight A As i j k := by
  classical
  induction As generalizing A i with
  | nil => simp [pathWeight, pathEntries]
  | cons B Bs ih =>
    change (∑ k, product (B :: Bs) k j * A i k) = _
    let e := Fin.consEquiv (fun _ : Fin (Bs.length + 1) => I)
    symm
    calc
      _ = ∑ t, pathWeight A (B :: Bs) i j (e t) := (e.sum_comp _).symm
      _ = _ := by
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro k _
        rw [ih, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro t _
        let v : Fin (Bs.length + 1) → I := @Fin.cons Bs.length (fun _ => I) k t
        change A i (v 0) * (pathEntries B Bs (v 0) j (Fin.tail v)).prod =
          pathWeight B Bs k j t * A i k
        simp only [v, Fin.cons_zero, Fin.tail_cons, pathWeight, mul_comm]

theorem product_zero_iff (A : Coeff I) (As : List (Coeff I)) (i j : I) :
    product (A :: As) i j = 0 ↔ ∀ k, HasZero A As i j k := by
  classical
  rw [product_expansion, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => zero_le _)]
  simp [pathWeight, HasZero]

theorem product_pos_iff (A : Coeff I) (As : List (Coeff I)) (i j : I) :
    0 < product (A :: As) i j ↔ ∃ k, AllPositive A As i j k := by
  classical
  rw [pos_iff_ne_zero, ne_eq, product_zero_iff, not_forall]
  apply exists_congr
  intro k
  constructor
  · intro h a ha
    exact pos_iff_ne_zero.mpr fun he => h (show 0 ∈ _ from he ▸ ha)
  · intro h hz
    exact (lt_irrefl 0) (h 0 hz)

theorem lip_chain_zero_iff (a : Step X bot I) (s : List (Step X bot I))
    (_h : U ⊆ dom (chain ((a :: s).map Prod.fst)))
    (_hs : Stepwise (fun p V M => M ∈ lipOn d p V) (a :: s) U) (i j : I) :
    product ((a :: s).map Prod.snd) i j = 0 ↔ ∀ k, HasZero a.2 (s.map Prod.snd) i j k :=
  product_zero_iff _ _ _ _

theorem coLip_chain_pos_iff (a : Step X bot I) (s : List (Step X bot I))
    (_h : U ⊆ dom (chain ((a :: s).map Prod.fst)))
    (_hs : Stepwise (fun p V M => M ∈ coLipOn d p V) (a :: s) U) (i j : I) :
    0 < product ((a :: s).map Prod.snd) i j ↔ ∃ k, AllPositive a.2 (s.map Prod.snd) i j k :=
  product_pos_iff _ _ _ _

section Channels

omit [Fintype I]

abbrev Channel (I : Type) := I × I

def scalarFeasible (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X)
    (c : Channel I) : Set ℝ≥0∞ :=
  {a | U ⊆ dom p ∧ ∀ x ∈ U, ∀ y ∈ U, d c.2 (p.func x) (p.func y) ≤ a * d c.1 x y}

def channelLip (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) (c : Channel I) : ℝ≥0∞ :=
  sInf (scalarFeasible d p U c)

variable {c : Channel I} {a b : ℝ≥0∞}

theorem scalar_mem_iff (hU : U ⊆ dom p) :
    a ∈ scalarFeasible d p U c ↔ ∀ x ∈ U, ∀ y ∈ U, d c.2 (p.func x) (p.func y) ≤ a * d c.1 x y :=
  ⟨And.right, And.intro hU⟩

theorem channelLip_empty (h : scalarFeasible d p U c = ∅) : channelLip d p U c = ⊤ := by
  simp [channelLip, h]

theorem scalar_up (ha : a ∈ scalarFeasible d p U c) (hab : a ≤ b) :
    b ∈ scalarFeasible d p U c :=
  ⟨ha.1, fun x hx y hy => (ha.2 x hx y hy).trans (mul_le_mul_left hab _)⟩

theorem scalar_above (h : channelLip d p U c < a) : a ∈ scalarFeasible d p U c := by
  obtain ⟨b, hb, hba⟩ := sInf_lt_iff.mp h
  exact scalar_up hb hba.le

theorem scalar_zero_input {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hin : d c.1 x y = 0) (hout : 0 < d c.2 (p.func x) (p.func y)) :
    scalarFeasible d p U c = ∅ ∧ channelLip d p U c = ⊤ := by
  have h : scalarFeasible d p U c = ∅ := Set.eq_empty_iff_forall_notMem.mpr fun a ha => by
    have hb := ha.2 x hx y hy
    rw [hin, mul_zero] at hb
    exact (not_lt_of_ge hb) hout
  exact ⟨h, channelLip_empty h⟩

theorem scalar_attained (hpos : 0 < channelLip d p U c) (hfin : channelLip d p U c < ⊤) :
    channelLip d p U c ∈ scalarFeasible d p U c := by
  have ht := scalar_above hfin
  refine ⟨ht.1, fun x hx y hy => ?_⟩
  by_cases hz : d c.1 x y = 0
  · simpa only [hz, mul_zero] using ht.2 x hx y hy
  by_cases hi : d c.1 x y = ⊤
  · simp [hi, ENNReal.mul_top hpos.ne']
  by_contra! h
  have hd := (ENNReal.lt_div_iff_mul_lt (Or.inl hz) (Or.inl hi)).2 h
  obtain ⟨b, hb, hb'⟩ := exists_between hd
  exact (not_lt_of_ge ((scalar_above hb).2 x hx y hy))
    ((ENNReal.lt_div_iff_mul_lt (Or.inl hz) (Or.inl hi)).1 hb')

theorem scalar_inf_zero (h : channelLip d p U c = 0) (ha : 0 < a) : a ∈ scalarFeasible d p U c :=
  scalar_above (by rw [h]; exact ha)

theorem channelLip_finite_iff :
    channelLip d p U c < ⊤ ↔ ∃ a < ⊤, a ∈ scalarFeasible d p U c := by
  constructor
  · intro h
    obtain ⟨a, ha, ha'⟩ := exists_between h
    exact ⟨a, ha', scalar_above ha⟩
  · rintro ⟨a, hfin, ha⟩
    exact (sInf_le ha).trans_lt hfin

def gapDist (i : Bool) (x y : Option Bool) : ℝ≥0∞ :=
  if x = y then 0 else if i = false ∨ x = none ∨ y = none then ⊤ else 1

theorem gapGauge (i : Bool) : ExtendedPseudoMetric (Option Bool) none (gapDist i) where
  nonabsorbing := ⟨some false, by simp⟩
  dist_self x := by simp [gapDist]
  symm x y := by simp only [gapDist, eq_comm (a := y) (b := x), or_comm (a := y = none)]
  isolate_bot x hx := by simp [gapDist, hx]
  triangle x y z := by
    by_cases hxy : x = y
    · subst y; simp [gapDist]
    by_cases hyz : y = z
    · subst z; simp [gapDist]
    by_cases hxz : x = z
    · simp [gapDist, hxz]
    by_cases hi : i = false
    · simp [gapDist, hi, hxy]
    by_cases hx : x = none
    · subst x; simp [gapDist, hxy, hxz]
    by_cases hz : z = none
    · subst z; simp [gapDist, hyz, hxz]
    by_cases hy : y = none <;> simp [gapDist, hxy, hxz, hyz, hi, hx, hy, hz]

theorem gap_example :
    let p : Operator (Option Bool) none := identity
    let U := dom p
    U.Nonempty ∧ U ⊆ dom p ∧ channelLip gapDist p U (false, true) = 0 ∧
      0 ∉ scalarFeasible gapDist p U (false, true) := by
  dsimp only
  let p : Operator (Option Bool) none := identity
  have feasible {a : ℝ≥0∞} (ha : 0 < a) : a ∈ scalarFeasible gapDist p (dom p) (false, true) := by
    refine ⟨Set.Subset.rfl, fun x hx y hy => ?_⟩
    by_cases h : x = y
    · simp [p, identity, h, gapDist]
    · simp [p, identity, gapDist, h, ENNReal.mul_top ha.ne']
  change (dom p).Nonempty ∧ _ ∧ channelLip gapDist p (dom p) (false, true) = 0 ∧ _
  refine ⟨⟨some false, by simp [p, identity, dom]⟩, Set.Subset.rfl, ?_, ?_⟩
  · by_contra h
    obtain ⟨a, ha, hb⟩ := exists_between (pos_iff_ne_zero.mpr h)
    exact (not_lt_of_ge (sInf_le (feasible ha))) hb
  · intro h
    have hb := h.2 (some false) (by simp [identity, dom]) (some true) (by simp [identity, dom])
    simp [identity, gapDist] at hb

end Channels

def Row (M : Coeff I) (i j : I) : Prop := ∀ k ≠ i, M k j = 0
def Col (M : Coeff I) (i j : I) : Prop := ∀ k ≠ j, M i k = 0
def Diagonal (M : Coeff I) : Prop := ∀ i j, i ≠ j → M i j = 0

def RowDecoupled (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) (j : I) : Prop :=
  ∃ M ∈ lipOn d p U, ∃ i, Row M i j

def ColDecoupled (d : I → X → X → ℝ≥0∞) (p : Operator X bot) (U : Set X) (i : I) : Prop :=
  ∃ M ∈ lipOn d p U, ∃ j, Col M i j

theorem term_remove [DecidableEq I] (i j : I) (x y : X) (h : L i j = 0) :
    L i j * d i x y = 0 ∧
    act L (fun k => d k x y) j = ∑ k ∈ Finset.univ.erase i, L k j * d k x y := by
  have hz : L i j * d i x y = 0 := by simp [h]
  exact ⟨hz, by simpa only [act, hz, add_zero] using
    (Finset.sum_erase_add Finset.univ (fun k => L k j * d k x y) (Finset.mem_univ i)).symm⟩

theorem row_bound (hL : L ∈ lipOn d p U) {i j : I} (hr : Row L i j) :
    ∀ x ∈ U, ∀ y ∈ U, d j (p.func x) (p.func y) ≤ L i j * d i x y := by
  classical
  intro x hx y hy
  refine (hL.2 x hx y hy j).trans_eq ?_
  exact Finset.sum_eq_single i (fun k _ hk => by simp [hr k hk]) (by simp)

theorem col_bound (_hL : L ∈ lipOn d p U) {i j : I} (hc : Col L i j) :
    ∀ x ∈ U, ∀ y ∈ U, ∀ k ≠ j, L i k * d i x y = 0 :=
  fun _ _ _ _ k hk => by simp [hc k hk]

theorem diagonal_upper (hL : L ∈ lipOn d p U) (hdiag : Diagonal L) (j : I) :
    ∀ x ∈ U, ∀ y ∈ U, d j (p.func x) (p.func y) ≤ L j j * d j x y :=
  row_bound hL (fun k hk => hdiag k j hk)

theorem row_two_sided (hL : L ∈ lipOn d p U) (hK : K ∈ coLipOn d p U) (j : I) (hr : Row L j j) :
    ∀ x ∈ U, ∀ y ∈ U, K j j * d j x y ≤ d j (p.func x) (p.func y) ∧
      d j (p.func x) (p.func y) ≤ L j j * d j x y :=
  fun x hx y hy => ⟨coLip_term hK hx hy j j, row_bound hL hr x hx y hy⟩

theorem diagonal_two_sided (hL : L ∈ lipOn d p U) (hK : K ∈ coLipOn d p U) (hdiag : Diagonal L) :
    ∀ j, ∀ x ∈ U, ∀ y ∈ U, K j j * d j x y ≤ d j (p.func x) (p.func y) ∧
      d j (p.func x) (p.func y) ≤ L j j * d j x y :=
  fun j => row_two_sided hL hK j (fun k hk => hdiag k j hk)

theorem diagonal_two_sided_finite (hL : L ∈ lipOn d p U) (hK : K ∈ coLipOn d p U)
    (hdiag : Diagonal L) (hfin : ∀ j, L j j < ⊤ ∧ K j j < ⊤) :
    ∀ j, L j j < ⊤ ∧ K j j < ⊤ ∧
      ∀ x ∈ U, ∀ y ∈ U, K j j * d j x y ≤ d j (p.func x) (p.func y) ∧
        d j (p.func x) (p.func y) ≤ L j j * d j x y :=
  fun j => ⟨(hfin j).1, (hfin j).2, diagonal_two_sided hL hK hdiag j⟩

theorem coLip_pos (hK : K ∈ coLipOn d p U) {i j : I} (hij : 0 < K i j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hin : 0 < d i x y) : 0 < d j (p.func x) (p.func y) :=
  (ENNReal.mul_pos hij.ne' hin.ne').trans_le (coLip_term hK hx hy i j)

theorem coLip_reflects_zero (hK : K ∈ coLipOn d p U) (hdiag : ∀ j, 0 < K j j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hout : GaugeZeroRelated d (p.func x) (p.func y)) :
    GaugeZeroRelated d x y := by
  intro j
  by_contra h
  exact (coLip_pos hK (hdiag j) hx hy (pos_iff_ne_zero.mpr h)).ne' (hout j)

end

end HCH02
