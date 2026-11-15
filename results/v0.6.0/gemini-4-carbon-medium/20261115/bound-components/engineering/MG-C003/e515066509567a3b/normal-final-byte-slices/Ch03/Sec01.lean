import Ch03.Defs
 
namespace Ch03
 
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set Finset
 
/-! ### 命题 3.1：分量类型的矩阵约束 (CH03-P01-01 .. 03) -/
 
/-- CH03-P01-01: 命题 3.1(i) 常值分量输出零行上界。 -/
theorem prop_3_1_i_zero_row_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I)
    (_hU : U ⊆ dom ϕ) (hi : i ∈ I_const d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y ∧
      (∑ k : I, (0 : ENNReal) * d k x y) = 0 := by
  intro x hx y hy
  have h0 : d i (ϕ.func x) (ϕ.func y) = 0 := hi x hx y hy
  simp [h0]
 
/-- CH03-P01-01 补充：在任一受限 Lip 矩阵中将常值分量 `i` 对应输出行置零仍为合法受限 Lip 矩阵。 -/
theorem prop_3_1_i_zero_row_lip_matrix {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I)
    (L : I → I → ENNReal) (hL : IsLipMatrix d ϕ U L) (hi : i ∈ I_const d ϕ U) :
    IsLipMatrix d ϕ U (fun k j => if j = i then 0 else L k j) := by
  refine ⟨hL.1, fun x hx y hy j => ?_⟩
  by_cases hji : j = i
  · subst hji
    simp [hi x hx y hy]
  · simpa [hji] using hL.2 x hx y hy j
 
/-- CH03-P01-02: 命题 3.1(ii) 常值分量下存在正输入距离的源通道 co-Lip 条目必为零。 -/
theorem prop_3_1_ii_colip_entry_zero {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i k : I)
    (K : I → I → ENNReal) (_hU : U ⊆ dom ϕ)
    (hi : i ∈ I_const d ϕ U) (hK : IsCoLipMatrix d ϕ U K)
    (hpos : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) :
    K k i = 0 := by
  rcases hpos with ⟨x, hx, y, hy, hkpos⟩
  exact colip_entry_eq_zero_of_output_zero_input_pos d ϕ U K k i x y hK hx hy
    (hi x hx y hy) hkpos
 
/-- CH03-P01-03: 命题 3.1(iii) 恒等分量双向保距等式。 -/
theorem prop_3_1_iii_id_preserves_dist {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : Operator X bot) (U : Set X) (i : I)
    (_hU : U ⊆ dom ϕ) (hi : i ∈ I_id d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = d i x y := by
  intro x hx y hy
  have hx0 : d i (ϕ.func x) x = 0 := hi.2 x hx
  have hy0 : d i (ϕ.func y) y = 0 := hi.2 y hy
  apply le_antisymm
  · calc
      d i (ϕ.func x) (ϕ.func y)
          ≤ d i (ϕ.func x) x + d i x (ϕ.func y) := (hd i).triangle _ _ _
      _ ≤ d i (ϕ.func x) x + (d i x y + d i y (ϕ.func y)) :=
          add_le_add le_rfl ((hd i).triangle _ _ _)
      _ = d i x y := by
          rw [hx0, (hd i).symm y (ϕ.func y), hy0, zero_add, add_zero]
  · calc
      d i x y
          ≤ d i x (ϕ.func x) + d i (ϕ.func x) y := (hd i).triangle _ _ _
      _ ≤ d i x (ϕ.func x) + (d i (ϕ.func x) (ϕ.func y) + d i (ϕ.func y) y) :=
          add_le_add le_rfl ((hd i).triangle _ _ _)
      _ = d i (ϕ.func x) (ϕ.func y) := by
          rw [(hd i).symm x (ϕ.func x), hx0, hy0, zero_add, add_zero]
 
/-! ### 命题 3.2：复合下的有效分量包含与恒等分量保留 (CH03-P02-01 .. 03) -/
 
/-- 复合定义域包含关系：`U ⊆ dom(ϕ₂ ∘ ϕ₁)` 推出 `U ⊆ dom(ϕ₁)` 且 `ϕ₁(U) ⊆ dom(ϕ₂)`。 -/
theorem comp_dom_inclusions {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (hU : U ⊆ dom (ϕ₂ * ϕ₁)) :
    U ⊆ dom ϕ₁ ∧ operator_image ϕ₁ U ⊆ dom ϕ₂ := by
  refine ⟨fun x hx hbot => ?_, ?_⟩
  · have hc : (ϕ₂ * ϕ₁).func x ≠ bot := hU hx
    apply hc
    change ϕ₂.func (ϕ₁.func x) = bot
    rw [hbot, ϕ₂.preserves_bot]
  · rintro y ⟨x, hx, rfl⟩
    exact hU hx
 
/-- CH03-P02-03: 命题 3.2(iii) 恒等分量保留（同时排除常值优先分支）。 -/
theorem prop_3_2_iii_id_preserved {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (hU : U ⊆ dom (ϕ₂ * ϕ₁)) :
    I_id d ϕ₁ U ∩ I_id d ϕ₂ (operator_image ϕ₁ U) ⊆ I_id d (ϕ₂ * ϕ₁) U := by
  rcases comp_dom_inclusions ϕ₁ ϕ₂ U hU with ⟨hU1, hU2⟩
  rintro i ⟨hi1, hi2⟩
  refine ⟨?_, ?_⟩
  · intro hconst_comp
    apply hi1.1
    intro x hx y hy
    have hiso := prop_3_1_iii_id_preserves_dist d hd ϕ₂ (operator_image ϕ₁ U) i hU2 hi2
      (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
    rw [← hiso]
    exact hconst_comp x hx y hy
  · intro x hx
    apply le_antisymm _ (zero_le _)
    calc
      d i (ϕ₂.func (ϕ₁.func x)) x
          ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) + d i (ϕ₁.func x) x := (hd i).triangle _ _ _
      _ = 0 := by rw [hi2.2 (ϕ₁.func x) ⟨x, hx, rfl⟩, hi1.2 x hx, zero_add]
 
/-- CH03-P02-01: 命题 3.2(i) 两步复合的有效分量包含（在实际中间像域 `ϕ₁(U)` 上读取）。 -/
theorem prop_3_2_i_active_subset_union {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) (hU : U ⊆ dom (ϕ₂ * ϕ₁)) :
    I_act d (ϕ₂ * ϕ₁) U ⊆ I_act d ϕ₁ U ∪ I_act d ϕ₂ (operator_image ϕ₁ U) := by
  intro i hi
  by_contra hnot
  rw [Set.mem_union, not_or] at hnot
  rcases hnot with ⟨hn1, hn2⟩
  have h1 : i ∈ I_const d ϕ₁ U ∨ i ∈ I_id d ϕ₁ U := by
    by_contra hc; exact hn1 ⟨trivial, hc⟩
  have h2 : i ∈ I_const d ϕ₂ (operator_image ϕ₁ U) ∨ i ∈ I_id d ϕ₂ (operator_image ϕ₁ U) := by
    by_contra hc; exact hn2 ⟨trivial, hc⟩
  apply hi.2
  rcases h1 with hc1 | hid1 <;> rcases h2 with hc2 | hid2
  · -- (d) const + const
    left
    intro x hx y hy
    exact hc2 (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
  · -- (c) const + id
    left
    intro x hx y hy
    apply le_antisymm _ (zero_le _)
    calc
      d i (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y))
          ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) +
            d i (ϕ₁.func x) (ϕ₂.func (ϕ₁.func y)) := (hd i).triangle _ _ _
      _ ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) +
            (d i (ϕ₁.func x) (ϕ₁.func y) + d i (ϕ₁.func y) (ϕ₂.func (ϕ₁.func y))) :=
          add_le_add le_rfl ((hd i).triangle _ _ _)
      _ = 0 := by
          rw [hid2.2 (ϕ₁.func x) ⟨x, hx, rfl⟩, hc1 x hx y hy,
              (hd i).symm (ϕ₁.func y) (ϕ₂.func (ϕ₁.func y)),
              hid2.2 (ϕ₁.func y) ⟨y, hy, rfl⟩, zero_add, add_zero]
  · -- (b) id + const
    left
    intro x hx y hy
    exact hc2 (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
  · -- (a) id + id
    right
    exact prop_3_2_iii_id_preserved d hd ϕ₁ ϕ₂ U hU ⟨hid1, hid2⟩
 
/-- 有限复合链 `c_n = ϕ_n ∘ ⋯ ∘ ϕ_1`（0基索引：`chainCompSeq ϕs 0 = id_X`，`chainCompSeq ϕs (n+1) = ϕs n * chainCompSeq ϕs n`）。 -/
def chainCompSeq {X : Type} {bot : X} (ϕs : ℕ → Operator X bot) : ℕ → Operator X bot
  | 0 => operator_identity
  | n + 1 => ϕs n * chainCompSeq ϕs n
 
/-- 递归定义的实际中间像集 `U_{m+1} = ϕ_m(U_m)`（0基索引：`chainDomainSeq U₁ ϕs 0 = U₁`）。 -/
def chainDomainSeq {X : Type} {bot : X} (U₁ : Set X) (ϕs : ℕ → Operator X bot) : ℕ → Set X
  | 0 => U₁
  | m + 1 => operator_image (ϕs m) (chainDomainSeq U₁ ϕs m)
 
theorem chainDomainSeq_eq_image_chainCompSeq {X : Type} {bot : X}
    (U₁ : Set X) (ϕs : ℕ → Operator X bot) (n : ℕ) :
    chainDomainSeq U₁ ϕs n = operator_image (chainCompSeq ϕs n) U₁ := by
  induction n with
  | zero =>
      ext x
      simp [chainDomainSeq, chainCompSeq, operator_image, operator_identity]
  | succ n ih =>
      ext y
      simp only [chainDomainSeq, chainCompSeq, ih, operator_image, Set.mem_image]
      constructor
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(chainCompSeq ϕs n).func x, ⟨x, hx, rfl⟩, rfl⟩
 
theorem chainDomainSeq_subset_dom {X : Type} {bot : X}
    (U₁ : Set X) (ϕs : ℕ → Operator X bot) :
    ∀ n : ℕ, U₁ ⊆ dom (chainCompSeq ϕs n) →
      ∀ m < n, chainDomainSeq U₁ ϕs m ⊆ dom (ϕs m)
  | 0, _, m, hm => False.elim (Nat.not_lt_zero m hm)
  | n + 1, hU, m, hm => by
      rcases comp_dom_inclusions (chainCompSeq ϕs n) (ϕs n) U₁ hU with ⟨hUn, hImg⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
      · exact chainDomainSeq_subset_dom U₁ ϕs n hUn m hlt
      · simpa [chainDomainSeq_eq_image_chainCompSeq] using hImg
 
/-- CH03-P02-02 (零步基例): 空复合 `c_0 = id_X` 的有效分量为 `∅`。 -/
theorem prop_3_2_ii_zero_base {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (U₁ : Set X) :
    I_act d (operator_identity : Operator X bot) U₁ = ∅ := by
  ext i
  simp only [I_act, Set.mem_diff, Set.mem_univ, Set.mem_union, true_and,
    Set.mem_empty_iff_false, iff_false, not_not]
  by_cases hconst : i ∈ I_const d (operator_identity : Operator X bot) U₁
  · exact Or.inl hconst
  · exact Or.inr ⟨hconst, fun x _ => (hd i).dist_self x⟩
 
/-- CH03-P02-02: 命题 3.2(ii) 任意有限长度链的有效分量包含与非有效分量保持。 -/
theorem prop_3_2_ii_chain_active_subset {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕs : ℕ → Operator X bot) (U₁ : Set X) :
    ∀ n : ℕ, U₁ ⊆ dom (chainCompSeq ϕs n) →
      I_act d (chainCompSeq ϕs n) U₁ ⊆
        ⋃ m < n, I_act d (ϕs m) (chainDomainSeq U₁ ϕs m)
  | 0, _ => by
      simp [chainCompSeq, prop_3_2_ii_zero_base d hd U₁]
  | n + 1, hU => by
      rcases comp_dom_inclusions (chainCompSeq ϕs n) (ϕs n) U₁ hU with ⟨hUn, _⟩
      intro i hi
      have hstep := prop_3_2_i_active_subset_union d hd (chainCompSeq ϕs n) (ϕs n) U₁ hU hi
      rw [ ← chainDomainSeq_eq_image_chainCompSeq] at hstep
      rcases hstep with hprev | hlast
      · have hih := prop_3_2_ii_chain_active_subset d hd ϕs U₁ n hUn hprev
        rcases Set.mem_iUnion₂.mp hih with ⟨m, hm, hmem⟩
        exact Set.mem_iUnion₂.mpr ⟨m, Nat.lt_succ_of_lt hm, hmem⟩
      · exact Set.mem_iUnion₂.mpr ⟨n, Nat.lt_succ_self n, hlast⟩
 
theorem prop_3_2_ii_chain_nonactive_preserved {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕs : ℕ → Operator X bot) (U₁ : Set X) (n : ℕ) (i : I)
    (hU : U₁ ⊆ dom (chainCompSeq ϕs n))
    (hnonact : ∀ m < n, i ∉ I_act d (ϕs m) (chainDomainSeq U₁ ϕs m)) :
    i ∉ I_act d (chainCompSeq ϕs n) U₁ := by
  intro hi
  rcases Set.mem_iUnion₂.mp (prop_3_2_ii_chain_active_subset d hd ϕs U₁ n hU hi) with ⟨m, hm, hmem⟩
  exact hnonact m hm hmem
 
/-! ### 注：复合分量保持的逆向蕴含一般不成立 (CH03-P03-01) -/
 
/-- 两点换位空间 `𝒳 = {bot, a, b}`。 -/
inductive SwapSpace : Type
  | bot : SwapSpace
  | a : SwapSpace
  | b : SwapSpace
  deriving DecidableEq
 
def swapDist (_ : Unit) : SwapSpace → SwapSpace → ENNReal
  | .bot, .bot => 0
  | .a, .a => 0
  | .b, .b => 0
  | .a, .b => 1
  | .b, .a => 1
  | .bot, _ => ⊤
  | _, .bot => ⊤
 
theorem swapDist_is_extended :
    ∀ u : Unit, ExtendedPseudoMetric SwapSpace SwapSpace.bot (swapDist u) := by
  intro u
  refine
    { nonabsorbing := ⟨.a, by decide⟩
      dist_self := fun x => by cases x <;> rfl
      symm := fun x y => by cases x <;> cases y <;> rfl
      triangle := fun x y z => by cases x <;> cases y <;> cases z <;> simp [swapDist]
      isolate_bot := fun x hx => by cases x <;> simp_all [swapDist] }
 
def swapOp : Operator SwapSpace SwapSpace.bot where
  func
    | .bot => .bot
    | .a => .b
    | .b => .a
  preserves_bot := rfl
 
def swapU : Set SwapSpace := {.a, .b}
 
/-- CH03-P03-01: 两点换位例完整计算并同时否定命题 3.2(i) 与 (iii) 的逆向包含。 -/
theorem note_comp_converse_counterexample :
    swapU ⊆ dom (swapOp * swapOp) ∧
    operator_image swapOp swapU = swapU ∧
    I_act swapDist swapOp swapU = {()} ∧
    I_id swapDist swapOp swapU = ∅ ∧
    I_act swapDist swapOp (operator_image swapOp swapU) = {()} ∧
    I_id swapDist swapOp (operator_image swapOp swapU) = ∅ ∧
    I_id swapDist (swapOp * swapOp) swapU = {()} ∧
    I_act swapDist (swapOp * swapOp) swapU = ∅ ∧
    ¬ (I_act swapDist swapOp swapU ∪ I_act swapDist swapOp (operator_image swapOp swapU) ⊆
        I_act swapDist (swapOp * swapOp) swapU) ∧
    ¬ (I_id swapDist (swapOp * swapOp) swapU ⊆
        I_id swapDist swapOp swapU ∩ I_id swapDist swapOp (operator_image swapOp swapU)) := by
  have himg : operator_image swapOp swapU = swapU := by
    ext x
    cases x <;> simp [operator_image, swapU, swapOp]
  have hnconst_single : () ∉ I_const swapDist swapOp swapU := by
    intro hc
    have h := hc .a (by simp [swapU]) .b (by simp [swapU])
    simp [swapOp, swapDist] at h
  have hnid_single : () ∉ I_id swapDist swapOp swapU := by
    intro hid
    have h := hid.2 .a (by simp [swapU])
    simp [swapOp, swapDist] at h
  have hact_single : I_act swapDist swapOp swapU = {()} := by
    ext u
    cases u
    simp [I_act, hnconst_single, hnid_single]
  have hid_single : I_id swapDist swapOp swapU = ∅ := by
    ext u
    cases u
    simp [hnid_single]
  have hnconst_comp : () ∉ I_const swapDist (swapOp * swapOp) swapU := by
    intro hc
    have h := hc .a (by simp [swapU]) .b (by simp [swapU])
    change swapDist () (swapOp.func (swapOp.func .a)) (swapOp.func (swapOp.func .b)) = 0 at h
    simp [swapOp, swapDist] at h
  have hid_comp_mem : () ∈ I_id swapDist (swapOp * swapOp) swapU := by
    refine ⟨hnconst_comp, fun x hx => ?_⟩
    rcases hx with rfl | rfl <;> rfl
  have hid_comp : I_id swapDist (swapOp * swapOp) swapU = {()} := by
    ext u; cases u; simp [hid_comp_mem]
  have hact_comp : I_act swapDist (swapOp * swapOp) swapU = ∅ := by
    ext u; cases u; simp [I_act, hid_comp_mem]
  refine ⟨?_, himg, hact_single, hid_single, ?_, ?_, hid_comp, hact_comp, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> intro hbot <;> cases hbot
  · rw [himg, hact_single]
  · rw [himg, hid_single]
  · rw [himg, hact_single, hact_comp]
    simp
  · rw [himg, hid_comp, hid_single]
    simp
 
/-! ### 命题 3.3：常值分量的单侧保持与非封闭性 (CH03-P04-01 .. 02) -/
 
/-- CH03-P04-01: 命题 3.3(i) 外侧常值保持。 -/
theorem prop_3_3_i_outer_const_preserved {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ ψ : Operator X bot) (U : Set X) (i : I)
    (_hU : U ⊆ dom (ψ * ϕ))
    (hi : i ∈ I_const d ψ (operator_image ϕ U)) :
    i ∈ I_const d (ψ * ϕ) U := by
  intro x hx y hy
  exact hi (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩
 
/-- 七点空间 `𝒳 = {bot, a, b, p, q, r, s}`。 -/
inductive SevenSpace : Type
  | bot | a | b | p | q | r | s
  deriving DecidableEq
 
/-- 双分量指标集 `I = {idx_i, idx_m}`。 -/
inductive TwoIdx : Type
  | idx_i | idx_m
  deriving DecidableEq
 
instance : Fintype TwoIdx where
  elems := {.idx_i, .idx_m}
  complete x := by cases x <;> simp
 
instance : Nonempty TwoIdx := ⟨.idx_i⟩
 
/-- 将 `p, q` 合为零距类的标签映射（用于构造 `d_i`）。 -/
def sevenClassI : SevenSpace → Fin 5
  | .a => 0
  | .b => 1
  | .p => 2
  | .q => 2
  | .r => 3
  | .s => 4
  | .bot => 0
 
def sevenDist (k : TwoIdx) (x y : SevenSpace) : ENNReal :=
  if x = .bot ∧ y = .bot then 0
  else if x = .bot ∨ y = .bot then ⊤
  else match k with
    | .idx_i => if sevenClassI x = sevenClassI y then 0 else 1
    | .idx_m => if x = y then 0 else 1
 
theorem sevenDist_is_extended :
    ∀ k : TwoIdx, ExtendedPseudoMetric SevenSpace SevenSpace.bot (sevenDist k) := by
  intro k
  refine
    { nonabsorbing := ⟨.a, by decide⟩
      dist_self := fun x => by
        unfold sevenDist
        by_cases hx : x = .bot <;> cases k <;> simp [hx]
      symm := fun x y => by
        unfold sevenDist
        by_cases hx : x = .bot <;> by_cases hy : y = .bot <;>
          cases k <;> simp [hx, hy, eq_comm]
      triangle := fun x y z => by
        unfold sevenDist
        by_cases hx : x = .bot <;> by_cases hy : y = .bot <;> by_cases hz : z = .bot
        all_goals try simp [hx, hy, hz]
        cases k
        · dsimp only
          by_cases hxz : sevenClassI x = sevenClassI z
          · simp [hxz]
          · by_cases hxy : sevenClassI x = sevenClassI y
            · have hyz : sevenClassI y ≠ sevenClassI z := fun h => hxz (hxy.trans h)
              simp [hxy, hyz]
            · simp [hxz, hxy]
        · dsimp only
          by_cases hxz : x = z
          · simp [hxz]
          · by_cases hxy : x = y
            · have hyz : y ≠ z := fun h => hxz (hxy.trans h)
              simp [hxy, hyz]
            · simp [hxz, hxy]
      isolate_bot := fun x hx => by
        unfold sevenDist
        simp [hx] }
 
def sevenPhi : Operator SevenSpace SevenSpace.bot where
  func
    | .a => .p
    | .b => .q
    | _ => .bot
  preserves_bot := rfl
 
def sevenPsi : Operator SevenSpace SevenSpace.bot where
  func
    | .p => .r
    | .q => .s
    | _ => .bot
  preserves_bot := rfl
 
def sevenU : Set SevenSpace := {.a, .b}
 
/-- CH03-P04-02: 命题 3.3(ii) 内侧常值未必保持的合法七点双分量反例。 -/
theorem prop_3_3_ii_inner_const_counterexample :
    (∀ k : TwoIdx, ExtendedPseudoMetric SevenSpace SevenSpace.bot (sevenDist k)) ∧
    sevenU ⊆ dom (sevenPsi * sevenPhi) ∧
    TwoIdx.idx_i ∈ I_const sevenDist sevenPhi sevenU ∧
    sevenDist TwoIdx.idx_m (sevenPhi.func .a) (sevenPhi.func .b) = 1 ∧
    sevenDist TwoIdx.idx_i ((sevenPsi * sevenPhi).func .a) ((sevenPsi * sevenPhi).func .b) = 1 ∧
    TwoIdx.idx_i ∉ I_const sevenDist (sevenPsi * sevenPhi) sevenU := by
  refine ⟨sevenDist_is_extended, ?_, ?_, rfl, rfl, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> intro hbot <;> cases hbot
  · intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl
  · intro hconst
    have h := hconst .a (by simp [sevenU]) .b (by simp [sevenU])
    change sevenDist .idx_i (sevenPsi.func (sevenPhi.func .a))
      (sevenPsi.func (sevenPhi.func .b)) = 0 at h
    simp [sevenPhi, sevenPsi, sevenDist, sevenClassI] at h
 
/-! ### 推论 3.4：常值分量在复合中的保持条件 (CH03-P05-01) -/
 
/-- CH03-P05-01: 推论 3.4 外侧算子第 `j` 行除 `L j j` 外均为零时，内侧常值传给复合（允许 `L j j = ⊤`）。 -/
theorem cor_3_4_const_preserved_of_single_row {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ ψ : Operator X bot) (U : Set X) (j : I)
    (_hU : U ⊆ dom (ψ * ϕ))
    (hj : j ∈ I_const d ϕ U)
    (hexL : ∃ L : I → I → ENNReal,
      IsLipMatrix d ψ (operator_image ϕ U) L ∧ ∀ k : I, k ≠ j → L k j = 0) :
    j ∈ I_const d (ψ * ϕ) U := by
  rcases hexL with ⟨L, hL, hrow⟩
  intro x hx y hy
  have hbound := lip_bound_of_single_input_row d ψ (operator_image ϕ U) L j j hL hrow
    (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩
  rw [hj x hx y hy, mul_zero] at hbound
  exact le_antisymm hbound (zero_le _)
 
end Ch03
