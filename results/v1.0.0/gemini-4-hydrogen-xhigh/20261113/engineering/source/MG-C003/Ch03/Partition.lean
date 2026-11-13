import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.decoupling
import Mathlib.Tactic

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

section ComponentPartition

variable {X I : Type} {bot : X}

/-- 常值分量：输出在受限域 `U` 上两两零距的指标集合。 -/
def I_const (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set I :=
  { i | ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = 0 }

/-- 恒等分量：非常值且在受限域 `U` 上逐点与输入零距的指标集合（常值优先）。 -/
def I_id (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set I :=
  { i | i ∉ I_const d ϕ U ∧ ∀ x ∈ U, d i (ϕ.func x) x = 0 }

/-- 有效分量：既非常值也非恒等的其余指标集合。 -/
def I_act (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set I :=
  { i | i ∉ I_const d ϕ U ∧ i ∉ I_id d ϕ U }

/-- 全域常值分量。 -/
def I_const_global (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set I :=
  I_const d ϕ (dom ϕ)

/-- 全域恒等分量。 -/
def I_id_global (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set I :=
  I_id d ϕ (dom ϕ)

/-- 全域有效分量。 -/
def I_act_global (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set I :=
  I_act d ϕ (dom ϕ)

lemma I_act_eq_compl_union (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    I_act d ϕ U = (I_const d ϕ U ∪ I_id d ϕ U)ᶜ := by
  ext i
  simp [I_act]

@[simp] lemma op_mul_func (ϕ ψ : Operator X bot) (x : X) :
    (ϕ * ψ).func x = ϕ.func (ψ.func x) := rfl

@[simp] lemma op_one_func (x : X) :
    (1 : Operator X bot).func x = x := rfl

lemma component_partition_disjoint (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    Disjoint (I_const d ϕ U) (I_id d ϕ U) ∧
    Disjoint (I_const d ϕ U) (I_act d ϕ U) ∧
    Disjoint (I_id d ϕ U) (I_act d ϕ U) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Set.disjoint_left]
    intro i hi hhid
    exact hhid.1 hi
  · rw [Set.disjoint_left]
    intro i hi hact
    exact hact.1 hi
  · rw [Set.disjoint_left]
    intro i hi hact
    exact hact.2 hi

lemma component_partition_union (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) :
    I_const d ϕ U ∪ I_id d ϕ U ∪ I_act d ϕ U = Set.univ := by
  ext i
  simp [I_act]
  tauto

/-- **命题 3.1 (i)**：常值分量的输出 Lip 上界可取零行。 -/
theorem prop_3_1_const_lip_zero_row [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I)
    (_hU : U ⊆ dom ϕ) (hi : i ∈ I_const d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ (∑ k : I, (0 : ENNReal) * d k x y) ∧
      (∑ k : I, (0 : ENNReal) * d k x y) = 0 := by
  intro x hx y hy
  have hsum : (∑ k : I, (0 : ENNReal) * d k x y) = 0 := by simp
  rw [hsum, hi x hx y hy]
  exact ⟨le_rfl, rfl⟩

/-- 若 `ϕ` 在 `U` 上有合法 Lip 矩阵 `L` 且 `i` 为常值分量，将输出行 `i` 置零仍为合法 Lip 矩阵。 -/
theorem prop_3_1_const_zero_row_lip_matrix [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (L : I → I → ENNReal) (i : I)
    (hL : IsLipMatrix d ϕ U L) (hi : i ∈ I_const d ϕ U) :
    IsLipMatrix d ϕ U (fun k j => if j = i then 0 else L k j) := by
  refine ⟨hL.1, ?_⟩
  intro x hx y hy j
  by_cases hj : j = i
  · subst hj
    simp [hi x hx y hy]
  · simp [hj, hL.2 x hx y hy j]

/-- **命题 3.1 (ii)**：常值分量下，存在正输入距离的源分量对应 co-Lip 条目必为零。 -/
theorem prop_3_1_const_colip_zero [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (i k : I)
    (_hU : U ⊆ dom ϕ) (hi : i ∈ I_const d ϕ U)
    (hK : IsCoLipMatrix d ϕ U K)
    (hpos : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) :
    K k i = 0 := by
  rcases hpos with ⟨x, hx, y, hy, hdpos⟩
  exact colip_entry_eq_zero_of_output_zero_input_pos d ϕ U K k i x y hK hx hy
    (hi x hx y hy) hdpos

/-- **命题 3.1 (iii)**：恒等分量在受限域上保持该分量距离。 -/
theorem prop_3_1_id_isometry
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I)
    (hd : ExtendedPseudoMetric X bot (d i))
    (_hU : U ⊆ dom ϕ) (hi : i ∈ I_id d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = d i x y := by
  intro x hx y hy
  have hfx : d i (ϕ.func x) x = 0 := hi.2 x hx
  have hfy : d i (ϕ.func y) y = 0 := hi.2 y hy
  have hxfx : d i x (ϕ.func x) = 0 := by rw [hd.symm]; exact hfx
  have hyfy : d i y (ϕ.func y) = 0 := by rw [hd.symm]; exact hfy
  apply le_antisymm
  · calc
      d i (ϕ.func x) (ϕ.func y)
          ≤ d i (ϕ.func x) x + d i x (ϕ.func y) := hd.triangle _ _ _
      _ ≤ d i (ϕ.func x) x + (d i x y + d i y (ϕ.func y)) :=
          add_le_add le_rfl (hd.triangle _ _ _)
      _ = d i x y := by rw [hfx, hyfy, zero_add, add_zero]
  · calc
      d i x y
          ≤ d i x (ϕ.func x) + d i (ϕ.func x) y := hd.triangle _ _ _
      _ ≤ d i x (ϕ.func x) + (d i (ϕ.func x) (ϕ.func y) + d i (ϕ.func y) y) :=
          add_le_add le_rfl (hd.triangle _ _ _)
      _ = d i (ϕ.func x) (ϕ.func y) := by rw [hxfx, hfy, zero_add, add_zero]

lemma dom_comp_left {ϕ₁ ϕ₂ : Operator X bot} {U : Set X}
    (hU : U ⊆ dom (ϕ₂ * ϕ₁)) : U ⊆ dom ϕ₁ := by
  intro x hx
  have hne : ϕ₂.func (ϕ₁.func x) ≠ bot := hU hx
  intro hbot
  apply hne
  rw [hbot, ϕ₂.preserves_bot]

lemma dom_comp_right {ϕ₁ ϕ₂ : Operator X bot} {U : Set X}
    (hU : U ⊆ dom (ϕ₂ * ϕ₁)) : ϕ₁.func '' U ⊆ dom ϕ₂ := by
  rintro y ⟨x, hx, rfl⟩
  exact hU hx

/-- **命题 3.2 (i)**：两步复合下的有效分量包含。 -/
theorem prop_3_2_act_comp_two
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom (ϕ₂ * ϕ₁)) :
    I_act d (ϕ₂ * ϕ₁) U ⊆ I_act d ϕ₁ U ∪ I_act d ϕ₂ (ϕ₁.func '' U) := by
  intro i hi
  by_contra hnot
  have hnot1 : i ∉ I_act d ϕ₁ U := fun h => hnot (Or.inl h)
  have hnot2 : i ∉ I_act d ϕ₂ (ϕ₁.func '' U) := fun h => hnot (Or.inr h)
  have hcases1 : i ∈ I_const d ϕ₁ U ∨ i ∈ I_id d ϕ₁ U := by
    by_contra h
    push Not at h
    exact hnot1 ⟨h.1, h.2⟩
  have hcases2 : i ∈ I_const d ϕ₂ (ϕ₁.func '' U) ∨ i ∈ I_id d ϕ₂ (ϕ₁.func '' U) := by
    by_contra h
    push Not at h
    exact hnot2 ⟨h.1, h.2⟩
  have hU2 : ϕ₁.func '' U ⊆ dom ϕ₂ := dom_comp_right hU
  rcases hcases1 with h1c | h1id <;> rcases hcases2 with h2c | h2id
  · have hconst : i ∈ I_const d (ϕ₂ * ϕ₁) U := by
      intro x hx y hy
      exact h2c (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
    exact hi.1 hconst
  · have hconst : i ∈ I_const d (ϕ₂ * ϕ₁) U := by
      intro x hx y hy
      have h1 : d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) = 0 := h2id.2 _ ⟨x, hx, rfl⟩
      have h2 : d i (ϕ₁.func x) (ϕ₁.func y) = 0 := h1c x hx y hy
      have h3 : d i (ϕ₁.func y) (ϕ₂.func (ϕ₁.func y)) = 0 := by
        rw [(hd i).symm]
        exact h2id.2 _ ⟨y, hy, rfl⟩
      apply le_antisymm _ (zero_le _)
      calc
        d i ((ϕ₂ * ϕ₁).func x) ((ϕ₂ * ϕ₁).func y)
            = d i (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
        _ ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) + d i (ϕ₁.func x) (ϕ₂.func (ϕ₁.func y)) :=
            (hd i).triangle _ _ _
        _ ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) +
              (d i (ϕ₁.func x) (ϕ₁.func y) + d i (ϕ₁.func y) (ϕ₂.func (ϕ₁.func y))) :=
            add_le_add le_rfl ((hd i).triangle _ _ _)
        _ = 0 := by rw [h1, h2, h3, zero_add, zero_add]
    exact hi.1 hconst
  · have hconst : i ∈ I_const d (ϕ₂ * ϕ₁) U := by
      intro x hx y hy
      exact h2c (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
    exact hi.1 hconst
  · have hnot_const : i ∉ I_const d (ϕ₂ * ϕ₁) U := by
      intro hconst
      apply h1id.1
      intro x hx y hy
      have hiso := prop_3_1_id_isometry d ϕ₂ (ϕ₁.func '' U) i (hd i) hU2 h2id
        (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
      rw [← hiso]
      exact hconst x hx y hy
    have hid : i ∈ I_id d (ϕ₂ * ϕ₁) U := by
      refine ⟨hnot_const, ?_⟩
      intro x hx
      apply le_antisymm _ (zero_le _)
      calc
        d i ((ϕ₂ * ϕ₁).func x) x
            = d i (ϕ₂.func (ϕ₁.func x)) x := rfl
        _ ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) + d i (ϕ₁.func x) x :=
            (hd i).triangle _ _ _
        _ = 0 := by rw [h2id.2 _ ⟨x, hx, rfl⟩, h1id.2 x hx, zero_add]
    exact hi.2 hid

/-- **命题 3.2 (iii)**：恒等分量在两步复合下保持（常值优先分支已排除）。 -/
theorem prop_3_2_id_comp
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom (ϕ₂ * ϕ₁)) :
    I_id d ϕ₁ U ∩ I_id d ϕ₂ (ϕ₁.func '' U) ⊆ I_id d (ϕ₂ * ϕ₁) U := by
  intro i ⟨h1id, h2id⟩
  have hU2 : ϕ₁.func '' U ⊆ dom ϕ₂ := dom_comp_right hU
  have hnot_const : i ∉ I_const d (ϕ₂ * ϕ₁) U := by
    intro hconst
    apply h1id.1
    intro x hx y hy
    have hiso := prop_3_1_id_isometry d ϕ₂ (ϕ₁.func '' U) i (hd i) hU2 h2id
      (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
    rw [← hiso]
    exact hconst x hx y hy
  refine ⟨hnot_const, ?_⟩
  intro x hx
  apply le_antisymm _ (zero_le _)
  calc
    d i ((ϕ₂ * ϕ₁).func x) x
        = d i (ϕ₂.func (ϕ₁.func x)) x := rfl
    _ ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) + d i (ϕ₁.func x) x :=
        (hd i).triangle _ _ _
    _ = 0 := by rw [h2id.2 _ ⟨x, hx, rfl⟩, h1id.2 x hx, zero_add]

/-- 有限复合链 `c_n = ϕ_{n-1} ∘ ... ∘ ϕ_0`（`n = 0` 时为恒等算子）。 -/
def compPrefix (ϕ : ℕ → Operator X bot) : ℕ → Operator X bot
  | 0 => 1
  | n + 1 => ϕ n * compPrefix ϕ n

/-- 有限复合链沿各步像集产生的受限评估域序列：`orbitAt ϕ U 0 = U`，`orbitAt ϕ U (m+1) = ϕ_m(orbitAt ϕ U m)`。 -/
def orbitAt (ϕ : ℕ → Operator X bot) (U : Set X) : ℕ → Set X
  | 0 => U
  | m + 1 => (ϕ m).func '' orbitAt ϕ U m

/-- 与 `OperatorChain` 对齐的算子列表顺序。 -/
def chainList (ϕ : ℕ → Operator X bot) : ℕ → List (Operator X bot)
  | 0 => []
  | n + 1 => ϕ n :: chainList ϕ n

lemma compPrefix_eq_operatorChain (ϕ : ℕ → Operator X bot) (n : ℕ) :
    compPrefix ϕ n = OperatorChain (chainList ϕ n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [compPrefix, ih, chainList]
      rfl

lemma orbitAt_eq_image_compPrefix (ϕ : ℕ → Operator X bot) (U : Set X) (n : ℕ) :
    orbitAt ϕ U n = (compPrefix ϕ n).func '' U := by
  induction n with
  | zero =>
      ext z
      simp [orbitAt, compPrefix]
  | succ n ih =>
      rw [orbitAt, ih, compPrefix]
      ext z
      simp only [Set.mem_image, op_mul_func]
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(compPrefix ϕ n).func x, ⟨x, hx, rfl⟩, rfl⟩

lemma orbitAt_subset_dom_of_compPrefix (ϕ : ℕ → Operator X bot) (U : Set X) :
    ∀ n : ℕ, U ⊆ dom (compPrefix ϕ n) →
      (∀ m < n, U ⊆ dom (compPrefix ϕ m)) ∧
      (∀ m < n, orbitAt ϕ U m ⊆ dom (ϕ m)) := by
  intro n
  induction n with
  | zero =>
      intro _
      exact ⟨fun m hm => False.elim (Nat.not_lt_zero _ hm),
             fun m hm => False.elim (Nat.not_lt_zero _ hm)⟩
  | succ n ih =>
      intro hU
      have hU_prev : U ⊆ dom (compPrefix ϕ n) := dom_comp_left hU
      have h_right : (compPrefix ϕ n).func '' U ⊆ dom (ϕ n) := dom_comp_right hU
      rw [← orbitAt_eq_image_compPrefix] at h_right
      rcases ih hU_prev with ⟨ih1, ih2⟩
      refine ⟨?_, ?_⟩
      · intro m hm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
        · exact ih1 m hlt
        · exact hU_prev
      · intro m hm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
        · exact ih2 m hlt
        · exact h_right

/-- 零步复合（恒等算子）无有效分量。 -/
theorem prop_3_2_act_comp_zero
    (d : I → X → X → ENNReal) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) :
    I_act d (1 : Operator X bot) U = ∅ := by
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hi
  apply hi.2
  refine ⟨hi.1, ?_⟩
  intro x _
  exact (hd i).dist_self x

/-- **命题 3.2 (ii)**：任意有限长度链上的有效分量包含（含零步基例与实际像域递推）。 -/
theorem prop_3_2_act_comp_chain
    (d : I → X → X → ENNReal) (ϕ : ℕ → Operator X bot) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i)) :
    ∀ n : ℕ, U ⊆ dom (compPrefix ϕ n) →
      I_act d (compPrefix ϕ n) U ⊆ ⋃ m : Fin n, I_act d (ϕ m.1) (orbitAt ϕ U m.1) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [compPrefix, prop_3_2_act_comp_zero d U hd]
      exact Set.empty_subset _
  | succ n ih =>
      intro hU
      have hU_prev : U ⊆ dom (compPrefix ϕ n) := dom_comp_left hU
      have htwo := prop_3_2_act_comp_two d (compPrefix ϕ n) (ϕ n) U hd hU
      rw [← orbitAt_eq_image_compPrefix] at htwo
      intro i hi
      rcases htwo hi with hprev | hlast
      · obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (ih hU_prev hprev)
        exact Set.mem_iUnion.mpr ⟨m.castSucc, hm⟩
      · exact Set.mem_iUnion.mpr ⟨⟨n, Nat.lt_succ_self n⟩, hlast⟩

/-- **命题 3.2 (ii) 逆否形式**：若链中各步在实际像域上均非有效，则全复合也非有效。 -/
theorem prop_3_2_not_act_comp_chain
    (d : I → X → X → ENNReal) (ϕ : ℕ → Operator X bot) (U : Set X)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (n : ℕ) (hU : U ⊆ dom (compPrefix ϕ n)) (i : I)
    (hnone : ∀ m : Fin n, i ∉ I_act d (ϕ m.1) (orbitAt ϕ U m.1)) :
    i ∉ I_act d (compPrefix ϕ n) U := by
  intro hi
  obtain ⟨m, hm⟩ := Set.mem_iUnion.mp (prop_3_2_act_comp_chain d ϕ U hd n hU hi)
  exact hnone m hm

/-- **命题 3.3 (i)**：外侧算子在内侧像域上为常值分量时，复合仍为常值分量。 -/
theorem prop_3_3_const_comp_left
    (d : I → X → X → ENNReal) (ϕ ψ : Operator X bot) (U : Set X) (i : I)
    (_hU : U ⊆ dom (ψ * ϕ))
    (hi : i ∈ I_const d ψ (ϕ.func '' U)) :
    i ∈ I_const d (ψ * ϕ) U := by
  intro x hx y hy
  exact hi (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩

/-- **推论 3.4**：外侧算子在像域上指定输出行的非对角 Lip 系数全为零时，内侧常值分量传给复合。 -/
theorem cor_3_4_const_comp_preserve [Fintype I]
    (d : I → X → X → ENNReal) (ϕ ψ : Operator X bot) (U : Set X)
    (L : I → I → ENNReal) (j : I)
    (_hU : U ⊆ dom (ψ * ϕ))
    (hj : j ∈ I_const d ϕ U)
    (hL : IsLipMatrix d ψ (ϕ.func '' U) L)
    (hrow : ∀ k : I, k ≠ j → L k j = 0) :
    j ∈ I_const d (ψ * ϕ) U := by
  intro x hx y hy
  have hbound := lip_bound_of_single_input_row d ψ (ϕ.func '' U) L j j hL hrow
    (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩
  rw [hj x hx y hy, mul_zero] at hbound
  exact le_antisymm hbound (zero_le _)

end ComponentPartition

section Counterexamples31

open formal_oet.vol_01.ch_01_foundations

/-- 命题 3.2 后注记的反例空间：两点换位结构 `{bot, a, b}`。 -/
inductive SwapPt : Type
  | bot
  | a
  | b
  deriving DecidableEq

/-- 两点换位空间上的单分量距离。 -/
def swapDist : Unit → SwapPt → SwapPt → ENNReal
  | (), x, y =>
      if x = y then 0
      else if x = .bot ∨ y = .bot then ⊤
      else 1

lemma swapDist_is_extended :
    ∀ i : Unit, ExtendedPseudoMetric SwapPt .bot (swapDist i) := by
  intro ⟨⟩
  refine
    { nonabsorbing := ⟨.a, by decide⟩
      dist_self := by intro x; cases x <;> simp [swapDist]
      symm := by intro x y; cases x <;> cases y <;> simp [swapDist]
      triangle := by
        intro x y z
        cases x <;> cases y <;> cases z <;> simp [swapDist]
      isolate_bot := by
        intro x hx
        cases x
        · exact False.elim (hx rfl)
        · simp [swapDist]
        · simp [swapDist] }

/-- 对合换位算子：`a ↔ b`，`bot ↦ bot`。 -/
def swapOp : Operator SwapPt .bot where
  func
    | .bot => .bot
    | .a => .b
    | .b => .a
  preserves_bot := rfl

def swapU : Set SwapPt := {.a, .b}

/-- **注（复合分量保持的逆向蕴含一般不成立）**：合法两点换位例完整计算并同时否定两条逆向包含。 -/
theorem remark_comp_reverse_counterexample :
    swapU ⊆ dom (swapOp * swapOp) ∧
    swapOp.func '' swapU = swapU ∧
    I_act swapDist swapOp swapU = Set.univ ∧
    I_id swapDist swapOp swapU = ∅ ∧
    I_id swapDist (swapOp * swapOp) swapU = Set.univ ∧
    I_act swapDist (swapOp * swapOp) swapU = ∅ ∧
    ¬ (I_act swapDist swapOp swapU ∪ I_act swapDist swapOp (swapOp.func '' swapU) ⊆
        I_act swapDist (swapOp * swapOp) swapU) ∧
    ¬ (I_id swapDist (swapOp * swapOp) swapU ⊆
        I_id swapDist swapOp swapU ∩ I_id swapDist swapOp (swapOp.func '' swapU)) := by
  have hdom : swapU ⊆ dom (swapOp * swapOp) := by
    intro x hx
    rcases hx with rfl | rfl <;> simp [dom, swapOp]
  have himg : swapOp.func '' swapU = swapU := by
    ext x
    constructor
    · rintro ⟨y, rfl | rfl, rfl⟩
      · right; rfl
      · left; rfl
    · intro hx
      rcases hx with rfl | rfl
      · exact ⟨.b, Or.inr rfl, rfl⟩
      · exact ⟨.a, Or.inl rfl, rfl⟩
  have hnot_const_single : () ∉ I_const swapDist swapOp swapU := by
    intro h
    have h0 := h .a (Or.inl rfl) .b (Or.inr rfl)
    simp [swapOp, swapDist] at h0
  have hnot_id_single : () ∉ I_id swapDist swapOp swapU := by
    intro h
    have h0 := h.2 .a (Or.inl rfl)
    simp [swapOp, swapDist] at h0
  have hact_single : I_act swapDist swapOp swapU = Set.univ := by
    ext ⟨⟩
    simp [I_act, hnot_const_single, hnot_id_single]
  have hid_single : I_id swapDist swapOp swapU = ∅ := by
    ext ⟨⟩
    simp [hnot_id_single]
  have hnot_const_comp : () ∉ I_const swapDist (swapOp * swapOp) swapU := by
    intro h
    have h0 := h .a (Or.inl rfl) .b (Or.inr rfl)
    simp [swapOp, swapDist] at h0
  have hid_comp : I_id swapDist (swapOp * swapOp) swapU = Set.univ := by
    ext ⟨⟩
    simp only [Set.mem_univ, iff_true]
    refine ⟨hnot_const_comp, ?_⟩
    intro x hx
    rcases hx with rfl | rfl <;> simp [swapOp, swapDist]
  have hact_comp : I_act swapDist (swapOp * swapOp) swapU = ∅ := by
    ext ⟨⟩
    simp [I_act, hid_comp]
  refine ⟨hdom, himg, hact_single, hid_single, hid_comp, hact_comp, ?_, ?_⟩
  · intro hsub
    have : () ∈ I_act swapDist (swapOp * swapOp) swapU := by
      apply hsub
      left
      rw [hact_single]
      trivial
    rw [hact_comp] at this
    exact this
  · intro hsub
    have : () ∈ I_id swapDist swapOp swapU ∩ I_id swapDist swapOp (swapOp.func '' swapU) := by
      apply hsub
      rw [hid_comp]
      trivial
    rw [hid_single] at this
    exact this.1

/-- 命题 3.3 (ii) 的合法七点空间。 -/
inductive SevenPt : Type
  | bot
  | a
  | b
  | p
  | q
  | r
  | s
  deriving DecidableEq, Fintype

/-- 命题 3.3 (ii) 的双分量指标集。 -/
inductive TwoIdx : Type
  | i
  | m
  deriving DecidableEq, Fintype

/-- 非吸收元部分的分量距离（取值 0 或 1），便于有限决策验证三角不等式。 -/
def sevenNonBotDist : TwoIdx → SevenPt → SevenPt → ℕ
  | .i, x, y =>
      if x = y then 0
      else if (x = .p ∧ y = .q) ∨ (x = .q ∧ y = .p) then 0
      else 1
  | .m, x, y =>
      if x = y then 0 else 1

/-- 七点空间上的双分量扩展伪度量：`d_i` 仅将 `p, q` 合并为零距类，`d_m` 为离散度量。 -/
def sevenDist (k : TwoIdx) (x y : SevenPt) : ENNReal :=
  if x = y then 0
  else if x = .bot ∨ y = .bot then ⊤
  else (sevenNonBotDist k x y : ENNReal)

lemma sevenNonBotDist_self : ∀ k x, sevenNonBotDist k x x = 0 := by
  decide

lemma sevenNonBotDist_symm : ∀ k x y, sevenNonBotDist k x y = sevenNonBotDist k y x := by
  decide

lemma sevenNonBotDist_triangle :
    ∀ k x y z, sevenNonBotDist k x z ≤ sevenNonBotDist k x y + sevenNonBotDist k y z := by
  decide

lemma sevenDist_is_extended :
    ∀ k : TwoIdx, ExtendedPseudoMetric SevenPt .bot (sevenDist k) := by
  intro k
  refine
    { nonabsorbing := ⟨.a, by decide⟩
      dist_self := by
        intro x
        simp [sevenDist]
      symm := by
        intro x y
        by_cases hxy : x = y
        · subst hxy; simp [sevenDist]
        · have hyx : y ≠ x := Ne.symm hxy
          by_cases hbot : x = .bot ∨ y = .bot
          · have hbot' : y = .bot ∨ x = .bot := hbot.symm
            simp [sevenDist, hxy, hyx, hbot, hbot']
          · have hbot' : ¬ (y = .bot ∨ x = .bot) := fun h => hbot h.symm
            simp [sevenDist, hxy, hyx, hbot, hbot', sevenNonBotDist_symm]
      triangle := by
        intro x y z
        by_cases hxz : x = z
        · subst hxz; simp [sevenDist]
        · by_cases hbotxz : x = .bot ∨ z = .bot
          · rcases hbotxz with rfl | rfl
            · by_cases hy : y = .bot
              · subst hy; simp [sevenDist, hxz]
              · simp [sevenDist, hy, Ne.symm hy]
            · by_cases hy : y = .bot
              · subst hy; simp [sevenDist, hxz]
              · simp [sevenDist, hy]
          · have hxbot : x ≠ .bot := fun h => hbotxz (Or.inl h)
            have hzbot : z ≠ .bot := fun h => hbotxz (Or.inr h)
            by_cases hybot : y = .bot
            · subst hybot
              simp [sevenDist, hxbot, hzbot]
            · have hxy_bot : ¬ (x = .bot ∨ y = .bot) := by tauto
              have hyz_bot : ¬ (y = .bot ∨ z = .bot) := by tauto
              have h1 : sevenDist k x y = (sevenNonBotDist k x y : ENNReal) := by
                by_cases hxy : x = y
                · subst hxy; simp [sevenDist, sevenNonBotDist_self]
                · simp [sevenDist, hxy, hxy_bot]
              have h2 : sevenDist k y z = (sevenNonBotDist k y z : ENNReal) := by
                by_cases hyz : y = z
                · subst hyz; simp [sevenDist, sevenNonBotDist_self]
                · simp [sevenDist, hyz, hyz_bot]
              have h3 : sevenDist k x z = (sevenNonBotDist k x z : ENNReal) := by
                simp [sevenDist, hxz, hbotxz]
              rw [h1, h2, h3, ← Nat.cast_add]
              exact Nat.cast_le.mpr (sevenNonBotDist_triangle k x y z)
      isolate_bot := by
        intro x hx
        simp [sevenDist, hx] }

def sevenPhi : Operator SevenPt .bot where
  func
    | .a => .p
    | .b => .q
    | _ => .bot
  preserves_bot := rfl

def sevenPsi : Operator SevenPt .bot where
  func
    | .p => .r
    | .q => .s
    | _ => .bot
  preserves_bot := rfl

def sevenU : Set SevenPt := {.a, .b}

/-- **命题 3.3 (ii)**：七点双分量反例表明内侧常值分量在复合下未必保持。 -/
theorem prop_3_3_const_comp_right_counterexample :
    (∀ k : TwoIdx, ExtendedPseudoMetric SevenPt .bot (sevenDist k)) ∧
    sevenU ⊆ dom (sevenPsi * sevenPhi) ∧
    TwoIdx.i ∈ I_const sevenDist sevenPhi sevenU ∧
    TwoIdx.i ∉ I_const sevenDist (sevenPsi * sevenPhi) sevenU := by
  refine ⟨sevenDist_is_extended, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> simp [dom, sevenPhi, sevenPsi]
  · intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
      simp [sevenPhi, sevenDist, sevenNonBotDist]
  · intro h
    have h0 := h .a (Or.inl rfl) .b (Or.inr rfl)
    simp [sevenPhi, sevenPsi, sevenDist, sevenNonBotDist] at h0

end Counterexamples31

end Ch03
