import Ch03.Defs

namespace Ch03

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set Finset

/-!
# § 3.1 分量分划及其复合性质 (`CH03-P01-01` – `CH03-P05-01`)
-/

/-! ## 命题 3.1：分量类型的矩阵约束 (`CH03-P01-01`, `CH03-P01-02`, `CH03-P01-03`) -/

/-- `CH03-P01-01`：命题 3.1(i) — 若 `i ∈ I_const(ϕ | U)`，则输出分量 `i` 满足零行 Lip 上界不等式且右端为零。 -/
theorem prop_3_1_const_zero_row_bound {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I)
    (hU : U ⊆ dom ϕ) (hi : i ∈ constComponents d ϕ U) :
    (∀ x ∈ U, ∀ y ∈ U,
      d i (ϕ.func x) (ϕ.func y) ≤ ∑ k : I, (0 : ENNReal) * d k x y) ∧
    (∀ x ∈ U, ∀ y ∈ U, (∑ k : I, (0 : ENNReal) * d k x y) = 0) := by
  have _ := hU
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    rw [hi x hx y hy]
    exact zero_le _
  · intro _ _ _ _
    simp

/-- `CH03-P01-01`（矩阵证书形式）：任意受限 Lip 矩阵将常值分量 `i` 所在输出行置零后仍为合法受限 Lip 矩阵。 -/
theorem prop_3_1_const_lip_zero_row_update {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I)
    (L : I → I → ENNReal)
    (hL : IsLipMatrix d ϕ U L) (hi : i ∈ constComponents d ϕ U) :
    IsLipMatrix d ϕ U (fun k j => if j = i then 0 else L k j) := by
  refine ⟨hL.1, ?_⟩
  intro x hx y hy j
  by_cases hji : j = i
  · subst hji
    simp [hi x hx y hy]
  · simpa [hji] using hL.2 x hx y hy j

/-- `CH03-P01-02`：命题 3.1(ii) — 若 `i ∈ I_const(ϕ | U)` 且 `K ∈ K(ϕ)|_U`，则任一存在正距离输入点对的源分量 `k` 必有 `K_{k→i} = 0`。 -/
theorem prop_3_1_const_colip_entry_eq_zero {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    (K : I → I → ENNReal) (i k : I)
    (hi : i ∈ constComponents d ϕ U)
    (hK : IsCoLipMatrix d ϕ U K)
    (hpos : ∃ x ∈ U, ∃ y ∈ U, 0 < d k x y) :
    K k i = 0 := by
  rcases hpos with ⟨x, hx, y, hy, hd_pos⟩
  exact colip_entry_eq_zero_of_output_zero_input_pos d ϕ U K k i x y
    hK hx hy (hi x hx y hy) hd_pos

/-- `CH03-P01-03`：命题 3.1(iii) — 若 `i ∈ I_id(ϕ | U)`，则在 `U` 上保持 `d_i` 点对距离不变。 -/
theorem prop_3_1_id_preserves_dist {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i : I)
    (hdi : ExtendedPseudoMetric X bot (d i))
    (hU : U ⊆ dom ϕ) (hi : i ∈ idComponents d ϕ U) :
    ∀ x ∈ U, ∀ y ∈ U, d i (ϕ.func x) (ϕ.func y) = d i x y := by
  have _ := hU
  intro x hx y hy
  have hzx : d i (ϕ.func x) x = 0 := hi.2 x hx
  have hzy : d i (ϕ.func y) y = 0 := hi.2 y hy
  have hzy_symm : d i y (ϕ.func y) = 0 := by rw [hdi.symm y (ϕ.func y), hzy]
  have hzx_symm : d i x (ϕ.func x) = 0 := by rw [hdi.symm x (ϕ.func x), hzx]
  apply le_antisymm
  · calc
      d i (ϕ.func x) (ϕ.func y)
          ≤ d i (ϕ.func x) x + d i x (ϕ.func y) := hdi.triangle _ _ _
      _ ≤ d i (ϕ.func x) x + (d i x y + d i y (ϕ.func y)) :=
          add_le_add le_rfl (hdi.triangle _ _ _)
      _ = d i x y := by simp [hzx, hzy_symm]
  · calc
      d i x y
          ≤ d i x (ϕ.func x) + d i (ϕ.func x) y := hdi.triangle _ _ _
      _ ≤ d i x (ϕ.func x) + (d i (ϕ.func x) (ϕ.func y) + d i (ϕ.func y) y) :=
          add_le_add le_rfl (hdi.triangle _ _ _)
      _ = d i (ϕ.func x) (ϕ.func y) := by simp [hzx_symm, hzy]

/-! ## 命题 3.2：复合下的有效分量包含与恒等分量保留 (`CH03-P02-01`, `CH03-P02-02`, `CH03-P02-03`) -/

/-- `CH03-P02-03`：命题 3.2(iii) — 恒等分量保留（同时排除常值优先分支）：
`I_id(ϕ₁ | U) ∩ I_id(ϕ₂ | ϕ₁(U)) ⊆ I_id(ϕ₂ ∘ ϕ₁ | U)`。 -/
theorem prop_3_2_id_comp_preserved {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁)) :
    idComponents d ϕ₁ U ∩ idComponents d ϕ₂ (operator_image ϕ₁ U) ⊆
      idComponents d (operator_compose ϕ₂ ϕ₁) U := by
  obtain ⟨_, hU₂⟩ := dom_comp_subset ϕ₁ ϕ₂ U hU
  rintro i ⟨hi₁, hi₂⟩
  refine ⟨?_, ?_⟩
  · -- 排除常值优先分支：利用 ϕ₂ 在 ϕ₁(U) 上的恒等保距性与 i ∉ I_const(ϕ₁ | U)
    intro hconst_comp
    apply hi₁.1
    intro x hx y hy
    have hx_img : ϕ₁.func x ∈ operator_image ϕ₁ U := ⟨x, hx, rfl⟩
    have hy_img : ϕ₁.func y ∈ operator_image ϕ₁ U := ⟨y, hy, rfl⟩
    have hiso := prop_3_1_id_preserves_dist d ϕ₂ (operator_image ϕ₁ U) i (hd i) hU₂ hi₂
      (ϕ₁.func x) hx_img (ϕ₁.func y) hy_img
    rw [← hiso]
    exact hconst_comp x hx y hy
  · intro x hx
    have hx_img : ϕ₁.func x ∈ operator_image ϕ₁ U := ⟨x, hx, rfl⟩
    apply le_antisymm _ (zero_le _)
    calc
      d i ((operator_compose ϕ₂ ϕ₁).func x) x
          = d i (ϕ₂.func (ϕ₁.func x)) x := rfl
      _ ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) + d i (ϕ₁.func x) x :=
          (hd i).triangle _ _ _
      _ = 0 + 0 := by rw [hi₂.2 (ϕ₁.func x) hx_img, hi₁.2 x hx]
      _ = 0 := zero_add 0

/-- `CH03-P02-01`：命题 3.2(i) — 两步复合下的有效分量包含：
`I_act(ϕ₂ ∘ ϕ₁ | U) ⊆ I_act(ϕ₁ | U) ∪ I_act(ϕ₂ | ϕ₁(U))`。 -/
theorem prop_3_2_act_comp_two_step {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom (operator_compose ϕ₂ ϕ₁)) :
    actComponents d (operator_compose ϕ₂ ϕ₁) U ⊆
      actComponents d ϕ₁ U ∪ actComponents d ϕ₂ (operator_image ϕ₁ U) := by
  intro i hi_act
  by_contra hnot
  have hnot₁ : i ∉ actComponents d ϕ₁ U := fun h => hnot (Or.inl h)
  have hnot₂ : i ∉ actComponents d ϕ₂ (operator_image ϕ₁ U) := fun h => hnot (Or.inr h)
  have hor₁ : i ∈ constComponents d ϕ₁ U ∪ idComponents d ϕ₁ U := by
    by_contra h
    exact hnot₁ ⟨trivial, h⟩
  have hor₂ : i ∈ constComponents d ϕ₂ (operator_image ϕ₁ U) ∪
      idComponents d ϕ₂ (operator_image ϕ₁ U) := by
    by_contra h
    exact hnot₂ ⟨trivial, h⟩
  rcases hor₁ with hc₁ | hid₁
  · rcases hor₂ with hc₂ | hid₂
    · -- (d) 常值 + 常值
      apply hi_act.2
      left
      intro x hx y hy
      exact hc₂ (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
    · -- (c) 内侧常值 + 外侧恒等
      apply hi_act.2
      left
      intro x hx y hy
      have hx_img : ϕ₁.func x ∈ operator_image ϕ₁ U := ⟨x, hx, rfl⟩
      have hy_img : ϕ₁.func y ∈ operator_image ϕ₁ U := ⟨y, hy, rfl⟩
      have h1 : d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) = 0 := hid₂.2 _ hx_img
      have h2 : d i (ϕ₁.func x) (ϕ₁.func y) = 0 := hc₁ x hx y hy
      have h3 : d i (ϕ₁.func y) (ϕ₂.func (ϕ₁.func y)) = 0 := by
        rw [(hd i).symm]
        exact hid₂.2 _ hy_img
      apply le_antisymm _ (zero_le _)
      calc
        d i (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y))
            ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) +
                d i (ϕ₁.func x) (ϕ₂.func (ϕ₁.func y)) := (hd i).triangle _ _ _
        _ ≤ d i (ϕ₂.func (ϕ₁.func x)) (ϕ₁.func x) +
              (d i (ϕ₁.func x) (ϕ₁.func y) +
                d i (ϕ₁.func y) (ϕ₂.func (ϕ₁.func y))) :=
            add_le_add le_rfl ((hd i).triangle _ _ _)
        _ = 0 := by simp [h1, h2, h3]
  · rcases hor₂ with hc₂ | hid₂
    · -- (b) 内侧恒等 + 外侧常值
      apply hi_act.2
      left
      intro x hx y hy
      exact hc₂ (ϕ₁.func x) ⟨x, hx, rfl⟩ (ϕ₁.func y) ⟨y, hy, rfl⟩
    · -- (a) 恒等 + 恒等
      apply hi_act.2
      right
      exact prop_3_2_id_comp_preserved d hd ϕ₁ ϕ₂ U hU ⟨hid₁, hid₂⟩

/-- 有限算子链的复合算子 `c_n = ϕ_{n-1} ∘ ⋯ ∘ ϕ_0`（0-指标对应正文 `ϕ_n ∘ ⋯ ∘ ϕ_1`），其中 `c_0 = id_X`。 -/
def chainComp {X : Type} {bot : X} (ϕ : ℕ → Operator X bot) : ℕ → Operator X bot
  | 0 => operator_identity
  | n + 1 => operator_compose (ϕ n) (chainComp ϕ n)

/-- 有限算子链的实际中间像域递推：`U_0 = U_init`，`U_{m+1} = ϕ_m(U_m)`。 -/
def chainDomain {X : Type} {bot : X} (ϕ : ℕ → Operator X bot) (U_init : Set X) : ℕ → Set X
  | 0 => U_init
  | m + 1 => operator_image (ϕ m) (chainDomain ϕ U_init m)

/-- 实际中间像域与前 `m` 步复合像集一致：`U_m = c_m(U_init)`。 -/
theorem chainDomain_eq_operator_image {X : Type} {bot : X}
    (ϕ : ℕ → Operator X bot) (U_init : Set X) (m : ℕ) :
    chainDomain ϕ U_init m = operator_image (chainComp ϕ m) U_init := by
  induction m with
  | zero =>
      ext x
      simp [chainDomain, chainComp, operator_identity, operator_image]
  | succ m ih =>
      ext y
      simp only [chainDomain, ih, chainComp, operator_compose, operator_image,
        Set.mem_image, Function.comp_apply]
      constructor
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨(chainComp ϕ m).func x, ⟨x, hx, rfl⟩, rfl⟩

/-- 链初始域 `U_init ⊆ dom(c_n)` 保证每步前缀复合及单步中间像域均在相应定义域内。 -/
theorem chainDomain_subset_dom {X : Type} {bot : X}
    (ϕ : ℕ → Operator X bot) (U_init : Set X) (n : ℕ)
    (hU : U_init ⊆ dom (chainComp ϕ n)) :
    (∀ m ≤ n, U_init ⊆ dom (chainComp ϕ m)) ∧
    (∀ m < n, chainDomain ϕ U_init m ⊆ dom (ϕ m)) := by
  induction n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro m hm
        have hm0 : m = 0 := Nat.le_zero.mp hm
        subst hm0
        exact hU
      · intro m hm
        exact False.elim (Nat.not_lt_zero m hm)
  | succ n ih =>
      obtain ⟨hU_cn, himg_n⟩ := dom_comp_subset (chainComp ϕ n) (ϕ n) U_init hU
      obtain ⟨hpref, hstep⟩ := ih hU_cn
      refine ⟨?_, ?_⟩
      · intro m hm
        rcases Nat.of_le_succ hm with hmn | rfl
        · exact hpref m hmn
        · exact hU
      · intro m hm
        rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hlt | rfl
        · exact hstep m hlt
        · rw [chainDomain_eq_operator_image]
          exact himg_n

/-- `CH03-P02-02`（零步基例）：空复合 `c_0 = id_X` 在任意受限域上的有效分量集为空集。 -/
theorem prop_3_2_act_chain_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : ℕ → Operator X bot) (U₁ : Set X) :
    actComponents d (chainComp ϕ 0) U₁ = ∅ := by
  ext i
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hi_act
  apply hi_act.2
  by_cases hc : i ∈ constComponents d (chainComp ϕ 0) U₁
  · exact Or.inl hc
  · right
    refine ⟨hc, fun x _ => ?_⟩
    simpa [chainComp, operator_identity] using (hd i).dist_self x

/-- `CH03-P02-02`：命题 3.2(ii) — 任意有限长度链复合下的有效分量包含：
`I_act(c_n | U₁) ⊆ ⋃_{m < n} I_act(ϕ_m | U_m)`。 -/
theorem prop_3_2_act_chain {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : ℕ → Operator X bot) (U₁ : Set X) (n : ℕ)
    (hU₁ : U₁ ⊆ dom (chainComp ϕ n)) :
    actComponents d (chainComp ϕ n) U₁ ⊆
      ⋃ m < n, actComponents d (ϕ m) (chainDomain ϕ U₁ m) := by
  induction n with
  | zero =>
      rw [prop_3_2_act_chain_zero d hd ϕ U₁]
      exact Set.empty_subset _
  | succ n ih =>
      obtain ⟨hU_cn, _⟩ := dom_comp_subset (chainComp ϕ n) (ϕ n) U₁ hU₁
      intro i hi
      have htwo := prop_3_2_act_comp_two_step d hd (chainComp ϕ n) (ϕ n) U₁ hU₁ hi
      rw [← chainDomain_eq_operator_image] at htwo
      rcases htwo with hleft | hright
      · have hmem := ih hU_cn hleft
        rcases Set.mem_iUnion₂.mp hmem with ⟨m, hm, him⟩
        exact Set.mem_biUnion (Nat.lt_succ_of_lt hm) him
      · exact Set.mem_biUnion (Nat.lt_succ_self n) hright

/-- `CH03-P02-02`（逆否表述）：若每一步单体算子在对应受限像集 `U_m` 上均非有效，则全复合在 `U₁` 上也非有效。 -/
theorem prop_3_2_non_act_chain {X I : Type} {bot : X}
    (d : I → X → X → ENNReal)
    (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ : ℕ → Operator X bot) (U₁ : Set X) (n : ℕ) (i : I)
    (hU₁ : U₁ ⊆ dom (chainComp ϕ n))
    (hnon : ∀ m < n, i ∉ actComponents d (ϕ m) (chainDomain ϕ U₁ m)) :
    i ∉ actComponents d (chainComp ϕ n) U₁ := by
  intro hact
  have hmem := prop_3_2_act_chain d hd ϕ U₁ n hU₁ hact
  rcases Set.mem_iUnion₂.mp hmem with ⟨m, hm, him⟩
  exact hnon m hm him

/-! ## 注：复合分量保持的逆向蕴含一般不成立 (`CH03-P03-01`) -/

/-- 两点换位反例的底层空间 `X = {bot, a, b}`。 -/
inductive SwapSpace : Type
  | bot : SwapSpace
  | a : SwapSpace
  | b : SwapSpace
  deriving DecidableEq

/-- 两点换位反例上的单分量扩展伪度量：`d(a, b) = d(b, a) = 1`，自距 `0`，`bot` 隔离为 `⊤`。 -/
def swapDist : SwapSpace → SwapSpace → ENNReal
  | .bot, .bot => 0
  | .a, .a => 0
  | .b, .b => 0
  | .a, .b => 1
  | .b, .a => 1
  | .bot, _ => ⊤
  | _, .bot => ⊤

/-- `swapDist` 满足扩展伪度量公理。 -/
theorem swapDist_isExtendedPseudoMetric :
    ExtendedPseudoMetric SwapSpace SwapSpace.bot swapDist where
  nonabsorbing := ⟨.a, by decide⟩
  dist_self := by rintro (_ | _ | _) <;> rfl
  symm := by rintro (_ | _ | _) (_ | _ | _) <;> rfl
  triangle := by
    rintro (_ | _ | _) (_ | _ | _) (_ | _ | _) <;> simp [swapDist]
  isolate_bot := by
    rintro (_ | _ | _) h
    · exact False.elim (h rfl)
    · rfl
    · rfl

/-- 两点换位反例的单分量规范族。 -/
def swapGauge : Unit → SwapSpace → SwapSpace → ENNReal :=
  fun _ => swapDist

/-- 两点换位算子：`bot ↦ bot`，`a ↦ b`，`b ↦ a`。 -/
def swapOp : Operator SwapSpace SwapSpace.bot where
  func
    | .bot => .bot
    | .a => .b
    | .b => .a
  preserves_bot := rfl

/-- 两点换位反例的受限评估域 `U = {a, b}`。 -/
def swapSetU : Set SwapSpace := {.a, .b}

/-- `CH03-P03-01`：两点换位结构的合法性、两步有效与复合恒等的完整计算，以及对命题 3.2(i)/(iii) 两条逆向包含的同时否定。 -/
theorem remark_swap_counterexample_full :
    (∀ u : Unit, ExtendedPseudoMetric SwapSpace SwapSpace.bot (swapGauge u)) ∧
    swapSetU ⊆ dom (operator_compose swapOp swapOp) ∧
    operator_image swapOp swapSetU = swapSetU ∧
    actComponents swapGauge swapOp swapSetU = ({()} : Set Unit) ∧
    idComponents swapGauge swapOp swapSetU = (∅ : Set Unit) ∧
    actComponents swapGauge swapOp (operator_image swapOp swapSetU) = ({()} : Set Unit) ∧
    idComponents swapGauge swapOp (operator_image swapOp swapSetU) = (∅ : Set Unit) ∧
    idComponents swapGauge (operator_compose swapOp swapOp) swapSetU = ({()} : Set Unit) ∧
    actComponents swapGauge (operator_compose swapOp swapOp) swapSetU = (∅ : Set Unit) ∧
    ¬ (actComponents swapGauge swapOp swapSetU ∪
        actComponents swapGauge swapOp (operator_image swapOp swapSetU) ⊆
        actComponents swapGauge (operator_compose swapOp swapOp) swapSetU) ∧
    ¬ (actComponents swapGauge swapOp swapSetU ∩
        actComponents swapGauge swapOp (operator_image swapOp swapSetU) ⊆
        actComponents swapGauge (operator_compose swapOp swapOp) swapSetU) ∧
    ¬ (idComponents swapGauge (operator_compose swapOp swapOp) swapSetU ⊆
        idComponents swapGauge swapOp swapSetU ∩
          idComponents swapGauge swapOp (operator_image swapOp swapSetU)) := by
  have himg : operator_image swapOp swapSetU = swapSetU := by
    ext x
    cases x <;> simp [operator_image, swapOp, swapSetU]
  have hnot_const_step : () ∉ constComponents swapGauge swapOp swapSetU := by
    intro hc
    have h := hc .a (by simp [swapSetU]) .b (by simp [swapSetU])
    simp [swapGauge, swapOp, swapDist] at h
  have hnot_id_step : () ∉ idComponents swapGauge swapOp swapSetU := by
    intro hid
    have h := hid.2 .a (by simp [swapSetU])
    simp [swapGauge, swapOp, swapDist] at h
  have hact_step : actComponents swapGauge swapOp swapSetU = {()} := by
    ext u
    cases u
    simp [actComponents, hnot_const_step, hnot_id_step]
  have hid_step : idComponents swapGauge swapOp swapSetU = ∅ := by
    ext u
    cases u
    simp [hnot_id_step]
  have hnot_const_comp : () ∉ constComponents swapGauge (operator_compose swapOp swapOp) swapSetU := by
    intro hc
    have h := hc .a (by simp [swapSetU]) .b (by simp [swapSetU])
    simp [swapGauge, operator_compose, swapOp, swapDist] at h
  have hid_comp_mem : () ∈ idComponents swapGauge (operator_compose swapOp swapOp) swapSetU := by
    refine ⟨hnot_const_comp, ?_⟩
    intro x hx
    rcases hx with rfl | rfl <;> rfl
  have hid_comp : idComponents swapGauge (operator_compose swapOp swapOp) swapSetU = {()} := by
    ext u
    cases u
    simp [hid_comp_mem]
  have hact_comp : actComponents swapGauge (operator_compose swapOp swapOp) swapSetU = ∅ := by
    ext u
    cases u
    simp [actComponents, hid_comp_mem]
  refine ⟨fun _ => swapDist_isExtendedPseudoMetric, ?_, himg, hact_step, hid_step, ?_, ?_,
    hid_comp, hact_comp, ?_, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | rfl <;> simp [dom, operator_compose, swapOp]
  · rw [himg, hact_step]
  · rw [himg, hid_step]
  · rw [himg, hact_step, hact_comp]
    simp
  · rw [himg, hact_step, hact_comp]
    simp
  · rw [himg, hid_step, hid_comp]
    simp

/-! ## 命题 3.3：常值分量的单侧保持与非封闭性 (`CH03-P04-01`, `CH03-P04-02`) -/

/-- `CH03-P04-01`：命题 3.3(i) — 外侧常值保持：
`i ∈ I_const(ψ | ϕ(U)) ⟹ i ∈ I_const(ψ ∘ ϕ | U)`。 -/
theorem prop_3_3_outer_const_preserved {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ ψ : Operator X bot) (U : Set X)
    (hU : U ⊆ dom (operator_compose ψ ϕ)) :
    constComponents d ψ (operator_image ϕ U) ⊆
      constComponents d (operator_compose ψ ϕ) U := by
  have _ := hU
  intro i hi x hx y hy
  exact hi (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩

/-- 命题 3.3(ii) 的七点空间 `X = {bot, a, b, p, q, r, s}`。 -/
inductive SevenPt : Type
  | bot | a | b | p | q | r | s
  deriving DecidableEq

/-- 命题 3.3(ii) 的双分量指标集 `I = {i, m}`。 -/
inductive TwoIdx : Type
  | i | m
  deriving DecidableEq

instance : Fintype TwoIdx where
  elems := {.i, .m}
  complete := by rintro (_ | _) <;> simp

/-- 七点空间在 `d_i` 下的零距类代表映射（将 `p, q` 合并为同一类）。 -/
def sevenClassI : SevenPt → Fin 5
  | .bot => 0 -- unused on non-bot
  | .a => 0
  | .b => 1
  | .p => 2
  | .q => 2
  | .r => 3
  | .s => 4

/-- 七点双分量规范族：`d_i` 仅将 `(p, q)` 设为零距、其余不同类距离为 `1`；`d_m` 为非吸收点上的离散度量。 -/
def sevenDist (k : TwoIdx) (x y : SevenPt) : ENNReal :=
  if x = .bot ∧ y = .bot then 0
  else if x = .bot ∨ y = .bot then ⊤
  else match k with
    | .i => if sevenClassI x = sevenClassI y then 0 else 1
    | .m => if x = y then 0 else 1

/-- 由分类映射 `cls` 在非吸收点上诱导的离散类扩展伪度量通用引理。 -/
private theorem discrete_class_extended_pseudometric {X α : Type} [DecidableEq X] [DecidableEq α]
    (bot : X) (hnonabs : ∃ x : X, x ≠ bot) (cls : X → α) :
    ExtendedPseudoMetric X bot (fun x y =>
      if x = bot ∧ y = bot then 0
      else if x = bot ∨ y = bot then ⊤
      else if cls x = cls y then 0 else 1) where
  nonabsorbing := hnonabs
  dist_self x := by
    by_cases hx : x = bot <;> simp [hx]
  symm x y := by
    by_cases hx : x = bot <;> by_cases hy : y = bot
    · simp [hx, hy]
    · simp [hx, hy]
    · simp [hx, hy]
    · simp only [hx, hy, and_self, or_self, ↓reduceIte]
      by_cases hc : cls x = cls y
      · simp [hc]
      · have hcyx : cls y ≠ cls x := fun h => hc h.symm
        simp [hc, hcyx]
  triangle x y z := by
    by_cases hx : x = bot
    · by_cases hz : z = bot
      · simp [hx, hz]
      · by_cases hy : y = bot <;> simp [hx, hz, hy]
    · by_cases hz : z = bot
      · by_cases hy : y = bot <;> simp [hx, hz, hy]
      · by_cases hy : y = bot
        · simp [hx, hy, hz]
        · simp only [hx, hy, hz, and_self, or_self, ↓reduceIte]
          by_cases hxz : cls x = cls z
          · simp [hxz]
          · by_cases hxy : cls x = cls y
            · have hyz : cls y ≠ cls z := fun h => hxz (hxy.trans h)
              simp [hxy, hyz]
            · simp [hxz, hxy]
  isolate_bot x hx := by simp [hx]

/-- `sevenDist` 的两个分量均满足扩展伪度量公理。 -/
theorem sevenDist_isExtendedPseudoMetric :
    ∀ k : TwoIdx, ExtendedPseudoMetric SevenPt SevenPt.bot (sevenDist k) := by
  intro k
  cases k with
  | i =>
      simpa [sevenDist] using
        discrete_class_extended_pseudometric SevenPt.bot ⟨.a, by decide⟩ sevenClassI
  | m =>
      simpa [sevenDist] using
        discrete_class_extended_pseudometric SevenPt.bot ⟨.a, by decide⟩ id

/-- 七点反例中的内侧算子 `ϕ`：`a ↦ p`，`b ↦ q`，其余取 `bot`。 -/
def sevenPhi : Operator SevenPt SevenPt.bot where
  func
    | .a => .p
    | .b => .q
    | _ => .bot
  preserves_bot := rfl

/-- 七点反例中的外侧算子 `ψ`：`p ↦ r`，`q ↦ s`，其余取 `bot`。 -/
def sevenPsi : Operator SevenPt SevenPt.bot where
  func
    | .p => .r
    | .q => .s
    | _ => .bot
  preserves_bot := rfl

/-- 七点反例中的受限域 `U = {a, b}`。 -/
def sevenSetU : Set SevenPt := {.a, .b}

/-- `CH03-P04-02`：命题 3.3(ii) — 合法七点、双分量反例证明内侧常值分量在复合下未必保持：
`i ∈ I_const(ϕ | U)`（且 `ϕ(U)` 在 `d_m` 下可分辨），但 `i ∉ I_const(ψ ∘ ϕ | U)`。 -/
theorem prop_3_3_inner_const_not_preserved :
    (∀ k : TwoIdx, ExtendedPseudoMetric SevenPt SevenPt.bot (sevenDist k)) ∧
    sevenSetU ⊆ dom (operator_compose sevenPsi sevenPhi) ∧
    TwoIdx.i ∈ constComponents sevenDist sevenPhi sevenSetU ∧
    sevenDist TwoIdx.m (sevenPhi.func .a) (sevenPhi.func .b) = 1 ∧
    sevenDist TwoIdx.i ((operator_compose sevenPsi sevenPhi).func .a)
      ((operator_compose sevenPsi sevenPhi).func .b) = 1 ∧
    TwoIdx.i ∉ constComponents sevenDist (operator_compose sevenPsi sevenPhi) sevenSetU ∧
    ¬ (constComponents sevenDist sevenPhi sevenSetU ⊆
        constComponents sevenDist (operator_compose sevenPsi sevenPhi) sevenSetU) := by
  have hdom : sevenSetU ⊆ dom (operator_compose sevenPsi sevenPhi) := by
    intro x hx
    rcases hx with rfl | rfl <;> simp [dom, operator_compose, sevenPhi, sevenPsi]
  have hconst_in : TwoIdx.i ∈ constComponents sevenDist sevenPhi sevenSetU := by
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rfl
  have hnot_const_comp :
      TwoIdx.i ∉ constComponents sevenDist (operator_compose sevenPsi sevenPhi) sevenSetU := by
    intro hc
    have h := hc .a (by simp [sevenSetU]) .b (by simp [sevenSetU])
    simp [operator_compose, sevenPhi, sevenPsi, sevenDist, sevenClassI] at h
  refine ⟨sevenDist_isExtendedPseudoMetric, hdom, hconst_in, rfl, rfl, hnot_const_comp, ?_⟩
  intro hsub
  exact hnot_const_comp (hsub hconst_in)

/-! ## 推论 3.4：常值分量在复合中的保持条件 (`CH03-P05-01`) -/

/-- `CH03-P05-01`：推论 3.4 — 若 `j ∈ I_const(ϕ | U)` 且外侧算子 `ψ` 在 `ϕ(U)` 上存在输出第 `j` 行除对角项 `L j j` 外全为零的受限 Lip 矩阵（允许 `L j j = ⊤`），则 `j ∈ I_const(ψ ∘ ϕ | U)`。 -/
theorem cor_3_4_const_preserved_of_single_row_lip {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) (ϕ ψ : Operator X bot) (U : Set X) (j : I)
    (hU : U ⊆ dom (operator_compose ψ ϕ))
    (hj : j ∈ constComponents d ϕ U)
    (hL : ∃ L : I → I → ENNReal,
      IsLipMatrix d ψ (operator_image ϕ U) L ∧ ∀ k : I, k ≠ j → L k j = 0) :
    j ∈ constComponents d (operator_compose ψ ϕ) U := by
  have _ := hU
  rcases hL with ⟨L, hL_mat, hrow⟩
  intro x hx y hy
  have hsingle := lip_bound_of_single_input_row d ψ (operator_image ϕ U) L j j hL_mat hrow
    (ϕ.func x) ⟨x, hx, rfl⟩ (ϕ.func y) ⟨y, hy, rfl⟩
  apply le_antisymm _ (zero_le _)
  calc
    d j ((operator_compose ψ ϕ).func x) ((operator_compose ψ ϕ).func y)
        = d j (ψ.func (ϕ.func x)) (ψ.func (ϕ.func y)) := rfl
    _ ≤ L j j * d j (ϕ.func x) (ϕ.func y) := hsingle
    _ = L j j * 0 := by rw [hj x hx y hy]
    _ = 0 := mul_zero (L j j)

end Ch03
