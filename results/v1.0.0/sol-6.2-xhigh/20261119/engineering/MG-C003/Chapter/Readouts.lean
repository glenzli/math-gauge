import Chapter.Step

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter

namespace Affine

noncomputable def d : Unit → Option ℝ → Option ℝ → ℝ≥0∞ := fun _ => absDist
def f := liftRealMap (fun x => 2*x-1)
def U : Set (Option ℝ) := {some 0, some 1}

theorem gauge (i : Unit) : ExtendedPseudoMetric _ none (d i) := read_legal abs

theorem values :
    f.func (some 0) = some (-1) ∧ f.func (some 1) = some 1 ∧
    (f*f).func (some 0) = some (-3) ∧ (f*f).func (some 1) = some 1 := by
  norm_num [f]

theorem first :
    U ⊆ dom f ∧ fiber absDist f U (f.func (some 0)) = U ∧
      Const d f U = {()} ∧ Ident d f U = ∅ ∧ Active d f U = ∅ := by
  obtain ⟨h0,h1,_,_⟩ := values
  have hc : () ∈ Const d f U := by
    intro x hx y hy
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      norm_num [d,h0,h1]
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x hx
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> exact Option.some_ne_none _
  · exact Set.Subset.antisymm (fun _ hx => hx.1) (fun x hx => ⟨hx,hc x hx _ (by simp [U])⟩)
  all_goals
    ext i
    cases i
    simp [Active, Ident, hc]

theorem second :
    U ⊆ dom (f*f) ∧ fiber absDist (f*f) U ((f*f).func (some 0)) = {some 0} ∧
      Const d (f*f) U = ∅ ∧ Ident d (f*f) U = ∅ ∧ Active d (f*f) U = {()} := by
  obtain ⟨_,_,h0,h1⟩ := values
  have hne : () ∉ Const d (f*f) U := by
    intro h
    have he := h (some 0) (by simp [U]) (some 1) (by simp [U])
    change absDist ((f*f).func (some 0)) ((f*f).func (some 1)) = 0 at he
    norm_num [h0,h1,abs_zero] at he
  have hni : () ∉ Ident d (f*f) U := by
    intro h
    have he := h.2 (some 0) (by simp [U])
    change absDist ((f*f).func (some 0)) (some 0) = 0 at he
    norm_num [h0,abs_zero] at he
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro x hx
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> exact Option.some_ne_none _
  · apply Set.Subset.antisymm
    · rintro x ⟨hx,he⟩
      simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simp
      · norm_num [h0,h1,abs_zero] at he
    · intro x hx
      have he : x = some (0 : ℝ) := hx
      subst x
      exact ⟨by simp [U], (gauge ()).dist_self _⟩
  all_goals
    ext i
    cases i
    simp [Active, hne, hni]

theorem literal_constant (g : Operator (Option ℝ) none) (a : ℝ)
    (h : ∀ x ∈ U, g.func x = some a) :
    (∀ x ∈ U, (g*g).func x = g.func (some a)) ∧
    (U ⊆ dom (g*g) ↔ g.func (some a) ≠ none) ∧
    (U ⊆ dom (g*g) → fiber absDist (g*g) U ((g*g).func (some 0)) = U) ∧
    (g.func (some a) = none → U ∩ dom (g*g) = ∅) := by
  have he (x : Option ℝ) (hx : x ∈ U) : (g*g).func x = g.func (some a) := by
    rw [mul_func, h x hx]
  have h0 : some (0 : ℝ) ∈ U := by simp [U]
  refine ⟨he,⟨fun hd => (he _ h0) ▸ hd h0,
    fun hn x hx => show (g*g).func x ≠ none from (he x hx).symm ▸ hn⟩,?_ ,?_⟩
  · intro hd
    ext x
    exact ⟨fun hx => hx.1, fun hx => ⟨hx, by rw [he x hx, he _ h0]; exact (gauge ()).dist_self _⟩⟩
  · intro hb
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx,hd⟩
    exact hd ((he x hx).trans hb)

end Affine

namespace Translation

def f := liftRealMap (fun x => x + 1)
def U : Set (Option ℝ) := {some (-3),some (-2),some 0,some 2}
def V : Set (Option ℝ) := {some (-2),some (-1),some 1,some 3}

theorem gauge : ExtendedPseudoMetric (Option ℝ) none absDist := read_legal abs

theorem domains : U ⊆ dom f ∧ U ⊆ dom (1 : Operator (Option ℝ) none) := by
  have h : U ⊆ {x | x ≠ none} := by
    intro x hx
    simp only [U, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact Option.some_ne_none _
  refine ⟨?_,h⟩
  intro x hx
  cases x with
  | none => exact (h hx rfl).elim
  | some a => exact Option.some_ne_none _

theorem image : f.func '' U = V := by
  norm_num [f,U,V,Set.image_insert_eq]

theorem fiber_table (g : Operator (Option ℝ) none) (y : Option ℝ) (B : Set (Option ℝ))
    (hs : B ⊆ U)
    (h0 : absDist (g.func (some (-3))) y = 0 ↔ some (-3) ∈ B)
    (h1 : absDist (g.func (some (-2))) y = 0 ↔ some (-2) ∈ B)
    (h2 : absDist (g.func (some 0)) y = 0 ↔ some 0 ∈ B)
    (h3 : absDist (g.func (some 2)) y = 0 ↔ some 2 ∈ B) :
    fiber absDist g U y = B := by
  ext x
  by_cases h : x ∈ U
  · have he : x = some (-3) ∨ x = some (-2) ∨ x = some 0 ∨ x = some 2 := by
      simpa only [U,Set.mem_insert_iff,Set.mem_singleton_iff] using h
    rcases he with rfl | rfl | rfl | rfl
    · simpa only [fiber,Set.mem_setOf_eq,h,true_and] using h0
    · simpa only [fiber,Set.mem_setOf_eq,h,true_and] using h1
    · simpa only [fiber,Set.mem_setOf_eq,h,true_and] using h2
    · simpa only [fiber,Set.mem_setOf_eq,h,true_and] using h3
  · exact ⟨fun hx => (h hx.1).elim, fun hx => (h (hs hx)).elim⟩

@[simp] theorem identity_value (x : Option ℝ) : (1 : Operator (Option ℝ) none).func x = x := rfl

theorem partitions :
    fiberBlocks absDist (1 : Operator (Option ℝ) none) U =
      {{some (-3)}, {some (-2), some 2}, {some 0}} ∧
    fiberBlocks absDist f U =
      {{some (-3)}, {some (-2), some 0}, {some 2}} := by
  have a : fiber absDist (1 : Operator (Option ℝ) none) U (some (-3)) = {some (-3)} := by
    apply fiber_table <;> norm_num [U]
  have b : fiber absDist (1 : Operator (Option ℝ) none) U (some (-2)) = {some (-2),some 2} := by
    apply fiber_table <;> norm_num [U, Set.insert_subset_iff]
  have c : fiber absDist (1 : Operator (Option ℝ) none) U (some 0) = {some 0} := by
    apply fiber_table <;> norm_num [U]
  have e : fiber absDist (1 : Operator (Option ℝ) none) U (some 2) = {some (-2),some 2} := by
    apply fiber_table <;> norm_num [U, Set.insert_subset_iff]
  have a' : fiber absDist f U (some (-2)) = {some (-3)} := by
    apply fiber_table <;> norm_num [U,f]
  have b' : fiber absDist f U (some (-1)) = {some (-2),some 0} := by
    apply fiber_table <;> norm_num [U,f, Set.insert_subset_iff]
  have c' : fiber absDist f U (some 1) = {some (-2),some 0} := by
    apply fiber_table <;> norm_num [U,f, Set.insert_subset_iff]
  have e' : fiber absDist f U (some 3) = {some 2} := by
    apply fiber_table <;> norm_num [U,f]
  constructor
  · have hid : (1 : Operator (Option ℝ) none).func '' U = U := by simp
    rw [fiberBlocks,hid]
    conv_lhs => arg 2; unfold U
    simp only [Set.image_insert_eq, Set.image_singleton]
    rw [a,b,c,e]
    ext S
    simp
    tauto
  · rw [fiberBlocks,image]
    simp only [V, Set.image_insert_eq, Set.image_singleton,a',b',c',e']
    ext S
    simp

noncomputable def ε : ℝ≥0∞ := ENNReal.ofReal (3/2)

theorem cover_U : covering_number absDist ε U = 2 := by
  apply le_antisymm
  · apply two_center_upper (some (-2)) (some 0) (by simp [U]) (by simp [U])
    intro x hx
    simp only [U,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · left; norm_num [ε,absDist,ENNReal.ofReal_lt_ofReal_iff']
    · left; norm_num [ε,absDist,ENNReal.ofReal_lt_ofReal_iff']
    · right; norm_num [ε,absDist,ENNReal.ofReal_lt_ofReal_iff']
    · left; norm_num [ε,absDist,ENNReal.ofReal_lt_ofReal_iff']
  · apply two_center_lower ⟨some 0,by simp [U]⟩
    intro x hx
    simp only [U,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    have hε : 0 ≤ (3/2 : ℝ) := by norm_num
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨some 0,by simp [U],by norm_num [ε,absDist,ENNReal.ofReal_le_ofReal_iff, hε]⟩
    · exact ⟨some 0,by simp [U],by norm_num [ε,absDist,ENNReal.ofReal_le_ofReal_iff, hε]⟩
    · exact ⟨some 2,by simp [U],by norm_num [ε,absDist,ENNReal.ofReal_le_ofReal_iff, hε]⟩
    · exact ⟨some 0,by simp [U],by norm_num [ε,absDist,ENNReal.ofReal_le_ofReal_iff, hε]⟩

theorem cover_V : covering_number absDist ε V = 1 := by
  apply cover_single_center
  refine ⟨some (-2),by simp [V],?_⟩
  intro x hx
  simp only [V,Set.mem_insert_iff,Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl <;>
    norm_num [ε,absDist,ENNReal.ofReal_lt_ofReal_iff']

theorem covering_and_gap :
    covering_number absDist ε U = 2 ∧ covering_number absDist ε (f.func '' U) = 1 ∧
      ∃ h : GapDefined f absDist absDist U ε, entropyGap f absDist absDist U ε h = 1 := by
  have he : covering_number absDist ε (f.func '' U) = 1 := image.symm ▸ cover_V
  refine ⟨cover_U,he,Or.inr (he.trans_lt (by simp)),?_⟩
  norm_num [entropyGap, metric_entropy, log2_ereal, cover_U, he, Real.logb_self_eq_one]

end Translation
end Chapter
