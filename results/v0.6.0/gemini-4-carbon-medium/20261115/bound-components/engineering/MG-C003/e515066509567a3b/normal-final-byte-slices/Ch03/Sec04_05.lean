import Ch03.Sec03
 
namespace Ch03
 
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set Finset
 
/-! ### 3.4 输入尺度与零化阈值：引理 3.13 与命题 3.14 (CH03-P16-01 .. CH03-P17-04) -/
 
theorem ind01_eq_one_iff (P : Prop) : ind01 P = 1 ↔ P := by
  unfold ind01
  by_cases h : P <;> simp [h]
 
theorem ind01_eq_zero_iff (P : Prop) : ind01 P = 0 ↔ ¬ P := by
  unfold ind01
  by_cases h : P <;> simp [h]
 
def Regime11 {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (σ : I → Set X → ENNReal) (f : Operator X bot) (A : Set X) (τσ τN : ENNReal) :
    Set (I × I) :=
  {p | σ p.1 A < τσ ∧ τN ≤ uniformNullRadiusComp d f p.1 p.2 A}
 
def Regime10 {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (σ : I → Set X → ENNReal) (f : Operator X bot) (A : Set X) (τσ τN : ENNReal) :
    Set (I × I) :=
  {p | σ p.1 A < τσ ∧ uniformNullRadiusComp d f p.1 p.2 A < τN}
 
def Regime01 {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (σ : I → Set X → ENNReal) (f : Operator X bot) (A : Set X) (τσ τN : ENNReal) :
    Set (I × I) :=
  {p | τσ ≤ σ p.1 A ∧ τN ≤ uniformNullRadiusComp d f p.1 p.2 A}
 
def Regime00 {X I : Type} {bot : X} (d : I → X → X → ENNReal)
    (σ : I → Set X → ENNReal) (f : Operator X bot) (A : Set X) (τσ τN : ENNReal) :
    Set (I × I) :=
  {p | τσ ≤ σ p.1 A ∧ uniformNullRadiusComp d f p.1 p.2 A < τN}
 
/-- CH03-P16-01: 引理 3.13 四种阈值组合与 `channelType` 逐一对应，且互斥并穷尽 `I × I`。 -/
theorem lemma_3_13_four_regimes_exclusive_exhaustive {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : I → Set X → ENNReal)
    (f : Operator X bot) (A : Set X) (τσ τN : ENNReal)
    (_hA_ne : A.Nonempty) (_hA : A ⊆ dom f)
    (_hτσ0 : 0 < τσ) (_hτσtop : τσ < ⊤) (_hτN0 : 0 < τN) (_hτNtop : τN < ⊤) :
    (∀ p : I × I, p ∈ Regime11 d σ f A τσ τN ↔ channelType d σ f A τσ τN p.1 p.2 = (1, 1)) ∧
    (∀ p : I × I, p ∈ Regime10 d σ f A τσ τN ↔ channelType d σ f A τσ τN p.1 p.2 = (1, 0)) ∧
    (∀ p : I × I, p ∈ Regime01 d σ f A τσ τN ↔ channelType d σ f A τσ τN p.1 p.2 = (0, 1)) ∧
    (∀ p : I × I, p ∈ Regime00 d σ f A τσ τN ↔ channelType d σ f A τσ τN p.1 p.2 = (0, 0)) ∧
    Disjoint (Regime11 d σ f A τσ τN) (Regime10 d σ f A τσ τN) ∧
    Disjoint (Regime11 d σ f A τσ τN) (Regime01 d σ f A τσ τN) ∧
    Disjoint (Regime11 d σ f A τσ τN) (Regime00 d σ f A τσ τN) ∧
    Disjoint (Regime10 d σ f A τσ τN) (Regime01 d σ f A τσ τN) ∧
    Disjoint (Regime10 d σ f A τσ τN) (Regime00 d σ f A τσ τN) ∧
    Disjoint (Regime01 d σ f A τσ τN) (Regime00 d σ f A τσ τN) ∧
    Regime11 d σ f A τσ τN ∪ Regime10 d σ f A τσ τN ∪
      Regime01 d σ f A τσ τN ∪ Regime00 d σ f A τσ τN = Set.univ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p
    simp [Regime11, channelType, Prod.ext_iff, ind01_eq_one_iff]
  · intro p
    simp [Regime10, channelType, Prod.ext_iff, ind01_eq_one_iff, ind01_eq_zero_iff]
  · intro p
    simp [Regime01, channelType, Prod.ext_iff, ind01_eq_one_iff, ind01_eq_zero_iff]
  · intro p
    simp [Regime00, channelType, Prod.ext_iff, ind01_eq_zero_iff]
  · exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h1.2 h2.2)
  · exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h2.1 h1.1)
  · exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h2.1 h1.1)
  · exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h2.1 h1.1)
  · exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h2.1 h1.1)
  · exact Set.disjoint_left.mpr (fun _ h1 h2 => not_lt_of_ge h1.2 h2.2)
  · ext p
    simp only [Regime11, Regime10, Regime01, Regime00, Set.mem_union, Set.mem_setOf_eq,
      Set.mem_univ, iff_true]
    rcases lt_or_ge (σ p.1 A) τσ with hσ | hσ <;>
      rcases lt_or_ge (uniformNullRadiusComp d f p.1 p.2 A) τN with hr | hr
    · exact Or.inl (Or.inl (Or.inr ⟨hσ, hr⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨hσ, hr⟩))
    · exact Or.inr ⟨hσ, hr⟩
    · exact Or.inl (Or.inr ⟨hσ, hr⟩)
 
/-- CH03-P16-02: 引理 3.13(i) 输入尺度阈值 `τσ` 增大时，第一项取 `1` 的通道集合单调不减。 -/
theorem lemma_3_13_i_first_coord_mono {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : I → Set X → ENNReal)
    (f : Operator X bot) (A : Set X) (τσ τσ' τN : ENNReal)
    (hτ : τσ ≤ τσ') :
    {p : I × I | (channelType d σ f A τσ τN p.1 p.2).1 = 1} ⊆
      {p : I × I | (channelType d σ f A τσ' τN p.1 p.2).1 = 1} := by
  intro p hp
  simp only [Set.mem_setOf_eq, channelType, ind01_eq_one_iff] at hp ⊢
  exact lt_of_lt_of_le hp hτ
 
/-- CH03-P16-03: 引理 3.13(ii) 零化阈值 `τN` 增大时，第二项取 `1` 的通道集合单调不增。 -/
theorem lemma_3_13_ii_second_coord_antitone {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (σ : I → Set X → ENNReal)
    (f : Operator X bot) (A : Set X) (τσ τN τN' : ENNReal)
    (hτ : τN ≤ τN') :
    {p : I × I | (channelType d σ f A τσ τN' p.1 p.2).2 = 1} ⊆
      {p : I × I | (channelType d σ f A τσ τN p.1 p.2).2 = 1} := by
  intro p hp
  simp only [Set.mem_setOf_eq, channelType, ind01_eq_one_iff] at hp ⊢
  exact le_trans hτ hp
 
/-- CH03-P17-01: 命题 3.14(i) 任意单调尺度函数族在域缩小下的单调性及阈值推论。 -/
theorem prop_3_14_i_scale_mono_on_subset {X I : Type} {bot : X}
    (σ : I → Set X → ENNReal) (hσ : IsInputScaleFamily σ)
    (f : Operator X bot) (A B : Set X) (τσ : ENNReal) (i : I)
    (hB_ne : B.Nonempty) (hBA : B ⊆ A) (_hA : A ⊆ dom f) :
    σ i B ≤ σ i A ∧ (σ i A < τσ → σ i B < τσ) := by
  have hA_ne : A.Nonempty := hB_ne.mono hBA
  have hle := hσ i hB_ne hA_ne hBA
  exact ⟨hle, fun hlt => lt_of_le_of_lt hle hlt⟩
 
/-- CH03-P17-02: 命题 3.14(ii-a) 固定基点 `x ∈ B` 时，缩小评估域 `B ⊆ A` 使点态零化半径不减。 -/
theorem prop_3_14_ii_a_pointwise_radius_antitone {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot) (A B : Set X) (i j : I) (x : X)
    (_hx : x ∈ B) (hBA : B ⊆ A) (_hA : A ⊆ dom f) :
    pointwiseNullRadiusComp d f i j x A ≤ pointwiseNullRadiusComp d f i j x B := by
  apply sSup_le
  intro r hr
  apply le_sSup
  refine ⟨hr.1, hr.2.1, ?_⟩
  rintro z ⟨hz_ball, hzB⟩
  exact ⟨hzB, (hr.2.2 ⟨hz_ball, hBA hzB⟩).2⟩
 
/-- CH03-P17-03: 命题 3.14(ii-b) 同时缩小评估域与取 `inf` 的基点集合，统一零化半径单调不减。 -/
theorem prop_3_14_ii_b_uniform_radius_antitone {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (f : Operator X bot) (A B : Set X) (i j : I)
    (_hB_ne : B.Nonempty) (hBA : B ⊆ A) (hA : A ⊆ dom f) :
    uniformNullRadiusComp d f i j A ≤ uniformNullRadiusOn f (d i) (d j) B A ∧
    uniformNullRadiusOn f (d i) (d j) B A ≤ uniformNullRadiusComp d f i j B ∧
    uniformNullRadiusComp d f i j A ≤ uniformNullRadiusComp d f i j B := by
  have h1 : uniformNullRadiusComp d f i j A ≤ uniformNullRadiusOn f (d i) (d j) B A := by
    apply le_iInf₂
    intro x hxB
    exact iInf₂_le x (hBA hxB)
  have h2 : uniformNullRadiusOn f (d i) (d j) B A ≤ uniformNullRadiusComp d f i j B := by
    apply le_iInf₂
    intro x hxB
    exact le_trans (iInf₂_le x hxB)
      (prop_3_14_ii_a_pointwise_radius_antitone d f A B i j x hxB hBA hA)
  exact ⟨h1, h2, le_trans h1 h2⟩
 
/-- CH03-P17-04: 命题 3.14(iii) 直径尺度在 `A = {0, 1}, B = {0}, τσ = 1/2` 上的二点/单点反例，否定反向尺度判断。 -/
theorem prop_3_14_iii_reverse_scale_counterexample :
    let A : Set RealWithBot := {.val 0, .val 1}
    let B : Set RealWithBot := {.val 0}
    let f : Operator RealWithBot RealWithBot.bot := operator_identity
    let τσ : ENNReal := 1 / 2
    B.Nonempty ∧ B ⊆ A ∧ A ⊆ dom f ∧
    setDiam realStdDist B = 0 ∧
    setDiam realStdDist B < τσ ∧
    setDiam realStdDist A = 1 ∧
    τσ ≤ setDiam realStdDist A ∧
    ¬ (setDiam realStdDist B < τσ → setDiam realStdDist A < τσ) := by
  dsimp only
  have hB_diam : setDiam realStdDist ({RealWithBot.val 0} : Set RealWithBot) = 0 := by
    unfold setDiam
    apply le_antisymm _ (zero_le _)
    apply iSup₂_le
    rintro x rfl
    apply iSup₂_le
    rintro y rfl
    simp [realStdDist]
  have hA_diam : setDiam realStdDist ({RealWithBot.val 0, RealWithBot.val 1} : Set RealWithBot) = 1 := by
    unfold setDiam
    apply le_antisymm
    · apply iSup₂_le
      rintro x (rfl | rfl) <;> apply iSup₂_le <;> rintro y (rfl | rfl) <;>
        simp [realStdDist]
    · have h0 : RealWithBot.val 0 ∈ ({RealWithBot.val 0, RealWithBot.val 1} : Set RealWithBot) :=
        Set.mem_insert _ _
      have h1 : RealWithBot.val 1 ∈ ({RealWithBot.val 0, RealWithBot.val 1} : Set RealWithBot) :=
        Set.mem_insert_of_mem _ (Set.mem_singleton _)
      calc
        (1 : ENNReal) = realStdDist (RealWithBot.val 0) (RealWithBot.val 1) := by
          simp [realStdDist]
        _ ≤ ⨆ y ∈ ({RealWithBot.val 0, RealWithBot.val 1} : Set RealWithBot),
              realStdDist (RealWithBot.val 0) y :=
          le_iSup₂ (f := fun y _ => realStdDist (RealWithBot.val 0) y) (RealWithBot.val 1) h1
        _ ≤ ⨆ x ∈ ({RealWithBot.val 0, RealWithBot.val 1} : Set RealWithBot),
              ⨆ y ∈ ({RealWithBot.val 0, RealWithBot.val 1} : Set RealWithBot),
                realStdDist x y :=
          le_iSup₂ (f := fun x _ => ⨆ y ∈ ({RealWithBot.val 0, RealWithBot.val 1} : Set RealWithBot),
            realStdDist x y) (RealWithBot.val 0) h0
  have hlt : (0 : ENNReal) < 1 / 2 := by norm_num
  have hge : (1 / 2 : ENNReal) ≤ 1 := by norm_num
  have hB_ne : ({RealWithBot.val 0} : Set RealWithBot).Nonempty := ⟨.val 0, Set.mem_singleton _⟩
  have hBA : ({RealWithBot.val 0} : Set RealWithBot) ⊆ {.val 0, .val 1} := by
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact Set.mem_insert _ _
  have hA_dom : ({RealWithBot.val 0, RealWithBot.val 1} : Set RealWithBot) ⊆
      dom (operator_identity : Operator RealWithBot RealWithBot.bot) := by
    intro x hx hbot
    rcases hx with rfl | rfl <;> cases hbot
  refine ⟨hB_ne, hBA, hA_dom, hB_diam, ?_, hA_diam, ?_, ?_⟩
  · rw [hB_diam]; exact hlt
  · rw [hA_diam]; exact hge
  · rw [hB_diam, hA_diam]
    intro himp
    exact not_lt_of_ge hge (himp hlt)
 
/-! ### 3.5 局部零化与覆盖数：命题 3.15、3.16、反例与推论 3.17 (CH03-P18-01 .. CH03-P21-02) -/
 
/-- CH03-P18-01: 命题 3.15(i) 严格低于统一零化半径的输入点对输出必归零。 -/
theorem prop_3_15_i_lt_uniform_radius_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (A : Set X) (i j : I)
    (_hA_ne : A.Nonempty) (hA : A ⊆ dom f) :
    ∀ x ∈ A, ∀ y ∈ A, d i x y < uniformNullRadiusComp d f i j A →
      d j (f.func x) (f.func y) = 0 := by
  intro x hx y hy hlt
  have hlt_pt : d i x y < pointwiseNullRadiusComp d f i j x A :=
    lt_of_lt_of_le hlt (iInf₂_le x hx)
  exact (prop_3_11_lt_radius_zero d hd f A i j x y hA hx hy hlt_pt).2
 
/-- CH03-P18-02: 命题 3.15(ii) 输出正分离推出输入距离不小于统一零化半径。 -/
theorem prop_3_15_ii_pos_output_ge_uniform_radius {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (A : Set X) (i j : I)
    (hA_ne : A.Nonempty) (hA : A ⊆ dom f) :
    ∀ x ∈ A, ∀ y ∈ A, 0 < d j (f.func x) (f.func y) →
      uniformNullRadiusComp d f i j A ≤ d i x y := by
  intro x hx y hy hpos
  by_contra hnot
  push Not at hnot
  have h0 := prop_3_15_i_lt_uniform_radius_zero d hd f A i j hA_ne hA x hx y hy hnot
  exact (ne_of_gt hpos) h0
 
/-- CH03-P18-03: 命题 3.15(iii) 零化半径不足时的分离见证（含输出距离为 `+∞` 的情形）。 -/
theorem prop_3_15_iii_separation_witness {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (_hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (A : Set X) (i j : I) (τN α : ENNReal)
    (_hA_ne : A.Nonempty) (_hA : A ⊆ dom f)
    (_hτN0 : 0 < τN) (hτNtop : τN < ⊤)
    (hr_lt_α : uniformNullRadiusComp d f i j A < α) (hα_lt : α < τN) :
    ∃ x ∈ A, ∃ y ∈ A, ∃ ε : ENNReal,
      0 < ε ∧ ε < ⊤ ∧ d i x y < α ∧ ε ≤ d j (f.func x) (f.func y) := by
  have hα0 : 0 < α := lt_of_le_of_lt (zero_le _) hr_lt_α
  have hαtop : α < ⊤ := lt_trans hα_lt hτNtop
  have hex_y : ∃ y ∈ A, pointwiseNullRadiusComp d f i j y A < α := by
    by_contra hall
    push Not at hall
    exact not_lt_of_ge (le_iInf₂ hall) hr_lt_α
  rcases hex_y with ⟨y, hyA, hy_lt⟩
  have hnot_valid : ¬ ValidNullRadius f (d i) (d j) y A α :=
    fun hval => not_lt_of_ge (le_sSup (s := {r | ValidNullRadius f (d i) (d j) y A r}) hval) hy_lt
  have hex_x : ∃ x ∈ A, d i x y < α ∧ 0 < d j (f.func x) (f.func y) := by
    by_contra hno
    push Not at hno
    apply hnot_valid
    refine ⟨hα0, hαtop, ?_⟩
    rintro x ⟨hx_ball, hxA⟩
    exact ⟨hxA, le_antisymm (hno x hxA hx_ball) (zero_le _)⟩
  rcases hex_x with ⟨x, hxA, hdxy, hout_pos⟩
  refine ⟨x, hxA, y, hyA, min 1 (d j (f.func x) (f.func y)), ?_, ?_, hdxy, min_le_right _ _⟩
  · exact lt_min zero_lt_one hout_pos
  · exact lt_of_le_of_lt (min_le_left _ _) ENNReal.one_lt_top
 
/-- CH03-P19-01: 命题 3.16(i) 统一零化半径不小于有限正阈值 `τN` 时，每个基点的 `τN`-球包含于其计算纤维。 -/
theorem prop_3_16_i_ball_subset_fiber {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (A : Set X) (i j : I) (τN : ENNReal)
    (hA_ne : A.Nonempty) (hA : A ⊆ dom f)
    (_hτN0 : 0 < τN) (_hτNtop : τN < ⊤)
    (hr_ge : τN ≤ uniformNullRadiusComp d f i j A) :
    ∀ x ∈ A, ball (d i) x τN ∩ A ⊆ CompFiberSingle d f j (f.func x) A := by
  intro x hx y ⟨hy_ball, hyA⟩
  rw [CompFiberSingle_eq]
  refine ⟨hyA, ?_⟩
  have hlt : d i x y < uniformNullRadiusComp d f i j A := by
    rw [(hd i).symm x y]
    exact lt_of_lt_of_le hy_ball hr_ge
  rw [(hd j).symm (f.func y) (f.func x)]
  exact prop_3_15_i_lt_uniform_radius_zero d hd f A i j hA_ne hA x hx y hyA hlt
 
/-- CH03-P19-02: 命题 3.16(ii-a) 对任意 `B ⊆ A`（含空集与无有限内覆盖情形）构造内部输出中心并证明覆盖数不等式。 -/
theorem prop_3_16_ii_a_covering_number_le {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (A B : Set X) (i j : I) (τN ε : ENNReal)
    (hA_ne : A.Nonempty) (hA : A ⊆ dom f) (hBA : B ⊆ A)
    (hτN0 : 0 < τN) (hτNtop : τN < ⊤)
    (hε0 : 0 < ε) (_hεtop : ε < ⊤)
    (hr_ge : τN ≤ uniformNullRadiusComp d f i j A) :
    (∀ [DecidableEq X] (S : Finset X), InternalEpsilonNet (d i) τN B S →
      InternalEpsilonNet (d j) ε (operator_image f B) (S.image f.func) ∧
      (S.image f.func).card ≤ S.card) ∧
    covering_number (d j) ε (operator_image f B) ≤ covering_number (d i) τN B := by
  have hfib := prop_3_16_i_ball_subset_fiber d hd f A i j τN hA_ne hA hτN0 hτNtop hr_ge
  have hpush : ∀ [DecidableEq X] (S : Finset X), InternalEpsilonNet (d i) τN B S →
      InternalEpsilonNet (d j) ε (operator_image f B) (S.image f.func) ∧
      (S.image f.func).card ≤ S.card := by
    intro _ S hS
    refine ⟨⟨?_, ?_⟩, Finset.card_image_le⟩
    · intro z hz
      rcases Finset.mem_image.mp (Finset.mem_coe.mp hz) with ⟨s, hs, rfl⟩
      exact ⟨s, hS.1 hs, rfl⟩
    · rintro y ⟨a, haB, rfl⟩
      rcases hS.2 a haB with ⟨s, hsS, has⟩
      have hsB : s ∈ B := hS.1 hsS
      have hmem := hfib s (hBA hsB) ⟨has, hBA haB⟩
      rw [CompFiberSingle_eq] at hmem
      refine ⟨f.func s, Finset.mem_image_of_mem f.func hsS, ?_⟩
      rw [hmem.2]
      exact hε0
  refine ⟨hpush, ?_⟩
  classical
  apply le_iInf₂
  intro S hS
  rcases hpush S hS with ⟨hnet_out, hcard_le⟩
  calc
    covering_number (d j) ε (operator_image f B)
        ≤ ((S.image f.func).card : ENNReal) :=
      iInf_le_of_le (S.image f.func) (iInf_le_of_le hnet_out le_rfl)
    _ ≤ (S.card : ENNReal) := by exact_mod_cast hcard_le
 
/-- CH03-P19-03: 命题 3.16(ii-b) 当 `B` 非空时，由覆盖数不等式与 `log2` 单调性推出度量熵不等式。 -/
theorem prop_3_16_ii_b_metric_entropy_le {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (A B : Set X) (i j : I) (τN ε : ENNReal)
    (hA_ne : A.Nonempty) (hA : A ⊆ dom f) (hBA : B ⊆ A) (_hB_ne : B.Nonempty)
    (hτN0 : 0 < τN) (hτNtop : τN < ⊤)
    (hε0 : 0 < ε) (hεtop : ε < ⊤)
    (hr_ge : τN ≤ uniformNullRadiusComp d f i j A) :
    metric_entropy (d j) ε (operator_image f B) ≤ metric_entropy (d i) τN B := by
  exact log2_ereal_mono
    (prop_3_16_ii_a_covering_number_le d hd f A B i j τN ε
      hA_ne hA hBA hτN0 hτNtop hε0 hεtop hr_ge).2
 
/-- CH03-P20-01: 命题 3.16 后正文反例：在阶跃反例 `stepU` 上，对任意有限正 `τ` 选 `0 < a ≤ 1, 2a < τ`，构造二点集 `B = {-a, a}` 使输入覆盖数为 `1` 而输出在 `1/2` 尺度下覆盖数为 `2`。 -/
theorem post_prop_3_16_pointwise_pos_insufficient :
    (∀ y ∈ stepU, 0 < pointwiseNullRadius stepOp realStdDist realStdDist y stepU) ∧
    (∀ τ : ENNReal, 0 < τ → τ < ⊤ →
      ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2 * a) < τ ∧
        let B : Set RealWithBot := {.val (-a), .val a}
        B ⊆ stepU ∧
        covering_number realStdDist τ B = 1 ∧
        covering_number realStdDist (1 / 2) (operator_image stepOp B) = 2 ∧
        covering_number realStdDist τ B <
          covering_number realStdDist (1 / 2) (operator_image stepOp B)) ∧
    ¬ (∃ τ : ENNReal, 0 < τ ∧ τ < ⊤ ∧
      ∀ B ⊆ stepU,
        covering_number realStdDist (1 / 2) (operator_image stepOp B) ≤
          covering_number realStdDist τ B) := by
  have hpt := counterexample_3_1_pointwise_radius.2
  have hforall : ∀ τ : ENNReal, 0 < τ → τ < ⊤ →
      ∃ a : ℝ, 0 < a ∧ a ≤ 1 ∧ ENNReal.ofReal (2 * a) < τ ∧
        let B : Set RealWithBot := {.val (-a), .val a}
        B ⊆ stepU ∧
        covering_number realStdDist τ B = 1 ∧
        covering_number realStdDist (1 / 2) (operator_image stepOp B) = 2 ∧
        covering_number realStdDist τ B <
          covering_number realStdDist (1 / 2) (operator_image stepOp B) := by
    intro τ hτ0 hτtop
    have hτ_ne0 : τ ≠ 0 := ne_of_gt hτ0
    have hτ_netop : τ ≠ ⊤ := lt_top_iff_ne_top.mp hτtop
    have hτ_real_pos : 0 < τ.toReal := ENNReal.toReal_pos hτ_ne0 hτ_netop
    let a : ℝ := min 1 (τ.toReal / 4)
    have ha_pos : 0 < a := lt_min zero_lt_one (by linarith)
    have ha_le1 : a ≤ 1 := min_le_left _ _
    have ha_le_q : a ≤ τ.toReal / 4 := min_le_right _ _
    have h2a_lt_real : 2 * a < τ.toReal := by linarith
    have h2a_lt : ENNReal.ofReal (2 * a) < τ := by
      rw [← ENNReal.ofReal_toReal hτ_netop]
      exact (ENNReal.ofReal_lt_ofReal_iff hτ_real_pos).mpr h2a_lt_real
    let B : Set RealWithBot := {.val (-a), .val a}
    have hB_sub : B ⊆ stepU := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨-a, Or.inl ⟨by linarith, by linarith⟩, rfl⟩
      · exact ⟨a, Or.inr ⟨ha_pos, ha_le1⟩, rfl⟩
    have hcov_in : covering_number realStdDist τ B = 1 := by
      classical
      apply le_antisymm
      · have hnet : InternalEpsilonNet realStdDist τ B {RealWithBot.val a} := by
          refine ⟨fun z hz => ?_, fun z hz => ?_⟩
          · rw [Finset.coe_singleton, Set.mem_singleton_iff] at hz
            rw [hz]
            exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
          · refine ⟨RealWithBot.val a, Finset.mem_singleton_self _, ?_⟩
            rcases hz with rfl | rfl
            · change ENNReal.ofReal |-a - a| < τ
              have habs : |-a - a| = 2 * a := by
                have hneg : -a - a = -(2 * a) := by ring
                rw [hneg, abs_neg, abs_of_pos (by linarith)]
              rw [habs]
              exact h2a_lt
            · simpa [realStdDist] using hτ0
        exact le_trans (iInf_le_of_le {RealWithBot.val a} (iInf_le_of_le hnet le_rfl)) (by simp)
      · exact one_le_covering_number_of_nonempty realStdDist τ B ⟨.val (-a), Set.mem_insert _ _⟩
    have himg : operator_image stepOp B = {.val 0, .val 1} := by
      ext y
      simp only [operator_image, B, Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨z, rfl | rfl, rfl⟩
        · have hneg : -a < 0 := by linarith
          simp [stepOp, hneg]
        · have hnotneg : ¬ (a < 0) := by linarith
          simp [stepOp, hnotneg]
      · rintro (rfl | rfl)
        · refine ⟨.val (-a), Or.inl rfl, ?_⟩
          have hneg : -a < 0 := by linarith
          simp [stepOp, hneg]
        · refine ⟨.val a, Or.inr rfl, ?_⟩
          have hnotneg : ¬ (a < 0) := by linarith
          simp [stepOp, hnotneg]
    have hcov_out : covering_number realStdDist (1 / 2) (operator_image stepOp B) = 2 := by
      classical
      rw [himg]
      let Y : Set RealWithBot := {.val 0, .val 1}
      apply le_antisymm
      · let S2 : Finset RealWithBot := {.val 0, .val 1}
        have hnet2 : InternalEpsilonNet realStdDist (1 / 2) Y S2 := by
          refine ⟨fun z hz => ?_, fun z hz => ?_⟩
          · simpa [S2, Y] using hz
          · rcases hz with rfl | rfl
            · refine ⟨.val 0, by simp [S2], ?_⟩
              simp [realStdDist]
            · refine ⟨.val 1, by simp [S2], ?_⟩
              simp [realStdDist]
        have hcard2 : (S2.card : ENNReal) ≤ 2 := by
          have hc : S2.card = 2 := by
            rw [Finset.card_pair]
            intro heq
            have h01 := RealWithBot.val.inj heq
            norm_num at h01
          simp [hc]
        exact le_trans (iInf_le_of_le S2 (iInf_le_of_le hnet2 le_rfl)) hcard2
      · apply le_iInf₂
        intro S hS
        rcases hS.2 (.val 0) (Set.mem_insert _ _) with ⟨c0, hc0S, hd0⟩
        rcases hS.2 (.val 1) (Set.mem_insert_of_mem _ (Set.mem_singleton _)) with ⟨c1, hc1S, hd1⟩
        have hc0_eq : c0 = .val 0 := by
          rcases hS.1 hc0S with rfl | rfl
          · rfl
          · exfalso
            change ENNReal.ofReal |0 - 1| < 1 / 2 at hd0
            norm_num at hd0
        have hc1_eq : c1 = .val 1 := by
          rcases hS.1 hc1S with rfl | rfl
          · exfalso
            change ENNReal.ofReal |1 - 0| < 1 / 2 at hd1
            norm_num at hd1
          · rfl
        have hne01 : c0 ≠ c1 := by
          rw [hc0_eq, hc1_eq]
          intro heq
          have h01 := RealWithBot.val.inj heq
          norm_num at h01
        have h2le : 2 ≤ S.card := Finset.one_lt_card.mpr ⟨c0, hc0S, c1, hc1S, hne01⟩
        exact_mod_cast h2le
    refine ⟨a, ha_pos, ha_le1, h2a_lt, hB_sub, hcov_in, hcov_out, ?_⟩
    rw [hcov_in, hcov_out]
    norm_num
  refine ⟨hpt, hforall, ?_⟩
  rintro ⟨τ, hτ0, hτtop, hall⟩
  rcases hforall τ hτ0 hτtop with ⟨a, _, _, _, hB_sub, _, _, hlt⟩
  exact not_lt_of_ge (hall _ hB_sub) hlt
 
/-- CH03-P21-01: 推论 3.17 在 `diam_{d_i}(A) < τσ ≤ τN` 条件下，统一零化半径阈值与整体输出零距等价。 -/
theorem cor_3_17_small_domain_nullification_iff {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (A : Set X) (i j : I) (τσ τN : ENNReal)
    (hA_ne : A.Nonempty) (hA : A ⊆ dom f)
    (_hτσ0 : 0 < τσ) (_hτσtop : τσ < ⊤)
    (_hτN0 : 0 < τN) (hτNtop : τN < ⊤)
    (hdiam : setDiam (d i) A < τσ) (hτ : τσ ≤ τN) :
    τN ≤ uniformNullRadiusComp d f i j A ↔
      ∀ x ∈ A, ∀ y ∈ A, d j (f.func x) (f.func y) = 0 := by
  constructor
  · intro hr_ge x hx y hy
    have hdxy_le : d i x y ≤ setDiam (d i) A :=
      le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
    have hdxy_lt : d i x y < uniformNullRadiusComp d f i j A :=
      lt_of_le_of_lt hdxy_le (lt_of_lt_of_le hdiam (le_trans hτ hr_ge))
    exact prop_3_15_i_lt_uniform_radius_zero d hd f A i j hA_ne hA x hx y hy hdxy_lt
  · intro hconst
    have hj_const : ({j} : Set I) ⊆ I_const d f A := by
      rintro k rfl
      exact hconst
    have htop := (prop_3_8_i_b_const_subfamily_radius_top d f A {j} i
      hA_ne hA (Set.singleton_nonempty j) hj_const).2
    rw [uniformNullRadiusSubfamily_singleton] at htop
    change τN ≤ nullMatrix d f A j i
    rw [htop]
    exact le_of_lt hτNtop
 
/-- CH03-P21-02: 推论 3.17 等价条件成立且 `A` 非空时，任意有限正 `ε` 下的输出内覆盖数恰为 `1`。 -/
theorem cor_3_17_covering_number_eq_one {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (f : Operator X bot) (A : Set X) (i j : I) (τσ τN ε : ENNReal)
    (hA_ne : A.Nonempty) (hA : A ⊆ dom f)
    (hτσ0 : 0 < τσ) (hτσtop : τσ < ⊤)
    (hτN0 : 0 < τN) (hτNtop : τN < ⊤)
    (hε0 : 0 < ε) (_hεtop : ε < ⊤)
    (hdiam : setDiam (d i) A < τσ) (hτ : τσ ≤ τN)
    (hr_ge : τN ≤ uniformNullRadiusComp d f i j A) :
    covering_number (d j) ε (operator_image f A) = 1 := by
  have hconst := (cor_3_17_small_domain_nullification_iff d hd f A i j τσ τN
    hA_ne hA hτσ0 hτσtop hτN0 hτNtop hdiam hτ).mp hr_ge
  rcases hA_ne with ⟨a₀, ha₀⟩
  classical
  apply le_antisymm
  · have hnet : InternalEpsilonNet (d j) ε (operator_image f A) {f.func a₀} := by
      refine ⟨fun z hz => ?_, ?_⟩
      · rw [Finset.coe_singleton, Set.mem_singleton_iff] at hz
        rw [hz]
        exact ⟨a₀, ha₀, rfl⟩
      · rintro _ ⟨x, hxA, rfl⟩
        refine ⟨f.func a₀, Finset.mem_singleton_self _, ?_⟩
        rw [hconst x hxA a₀ ha₀]
        exact hε0
    exact le_trans (iInf_le_of_le {f.func a₀} (iInf_le_of_le hnet le_rfl)) (by simp)
  · exact one_le_covering_number_of_nonempty (d j) ε (operator_image f A) ⟨f.func a₀, a₀, ha₀, rfl⟩
 
end Ch03
