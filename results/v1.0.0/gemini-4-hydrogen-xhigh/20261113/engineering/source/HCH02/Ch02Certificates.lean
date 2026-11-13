import Ch02Matrices

/-!
# Chapter 2 — Lip / co-Lip Certificates, Composition, Perturbation, and Operator Chains

Formalizes obligations `HC02-D01`, `HC02-D02`, `HC02-D04`, `HC02-D05`, and
`HC02-P01` through `HC02-P17` from `source/02-operator-bounds.md`.
-/

namespace formal_oet.vol_01.ch_02_operator_bounds

open formal_oet.vol_01.ch_01_foundations

/-! ### Operator composition helpers and chain representations (HC02-D04, HC02-D05) -/

/-- Identity operator $\mathrm{id}_{\mathcal{X}} \in \mathcal{X}_{\mathrm{op}}$. -/
def idOperator {X : Type} {bot : X} : Operator X bot :=
  ⟨id, rfl⟩

@[simp]
theorem idOperator_func {X : Type} {bot : X} (x : X) :
    (idOperator (X := X) (bot := bot)).func x = x :=
  rfl

theorem dom_idOperator {X : Type} {bot : X} :
    dom (idOperator (X := X) (bot := bot)) = { x : X | x ≠ bot } :=
  rfl

/-- Composition $\psi \circ \phi$ of two operators in $\mathcal{X}_{\mathrm{op}}$. -/
def opComp {X : Type} {bot : X} (ψ ϕ : Operator X bot) : Operator X bot :=
  ⟨ψ.func ∘ ϕ.func, by simp [ϕ.preserves_bot, ψ.preserves_bot]⟩

@[simp]
theorem opComp_func {X : Type} {bot : X} (ψ ϕ : Operator X bot) (x : X) :
    (opComp ψ ϕ).func x = ψ.func (ϕ.func x) :=
  rfl

@[simp]
theorem opComp_idOperator {X : Type} {bot : X} (ϕ : Operator X bot) :
    opComp ϕ idOperator = ϕ := by
  ext x
  rfl

@[simp]
theorem idOperator_opComp {X : Type} {bot : X} (ϕ : Operator X bot) :
    opComp idOperator ϕ = ϕ := by
  ext x
  rfl

theorem opComp_assoc {X : Type} {bot : X} (χ ψ ϕ : Operator X bot) :
    opComp (opComp χ ψ) ϕ = opComp χ (opComp ψ ϕ) := by
  ext x
  rfl

/-- Common domain $\mathrm{dom}(\phi_1, \phi_2) = \mathrm{dom}(\phi_1) \cap \mathrm{dom}(\phi_2)$. -/
def commonDom₂ {X : Type} {bot : X} (ϕ₁ ϕ₂ : Operator X bot) : Set X :=
  dom ϕ₁ ∩ dom ϕ₂

theorem subset_dom_opComp_iff {X : Type} {bot : X}
    (ψ ϕ : Operator X bot) (U : Set X) :
    U ⊆ dom (opComp ψ ϕ) ↔ U ⊆ dom ϕ ∧ operator_image ϕ U ⊆ dom ψ := by
  constructor
  · intro hU
    refine ⟨?_, ?_⟩
    · intro x hx hbot
      have hx' : (opComp ψ ϕ).func x ≠ bot := hU hx
      simp [opComp, hbot, ψ.preserves_bot] at hx'
    · rintro y ⟨x, hx, rfl⟩
      exact hU hx
  · rintro ⟨_, hψ⟩ x hx
    exact hψ ⟨x, hx, rfl⟩

/-- Ordered finite operator composition $c_k = \phi_k \circ \cdots \circ \phi_1$
for execution sequence `ops : Fin k → Operator X bot`, with $c_0 = \mathrm{id}_{\mathcal{X}}$. -/
def opSeqComp {X : Type} {bot : X} :
    (k : ℕ) → (Fin k → Operator X bot) → Operator X bot
  | 0, _ => idOperator
  | k + 1, ops => opComp (ops (Fin.last k)) (opSeqComp k (fun m => ops m.castSucc))

@[simp]
theorem opSeqComp_zero {X : Type} {bot : X} (ops : Fin 0 → Operator X bot) :
    opSeqComp 0 ops = idOperator :=
  rfl

@[simp]
theorem opSeqComp_succ {X : Type} {bot : X} (k : ℕ) (ops : Fin (k + 1) → Operator X bot) :
    opSeqComp (k + 1) ops = opComp (ops (Fin.last k)) (opSeqComp k (fun m => ops m.castSucc)) :=
  rfl

@[simp]
theorem opSeqComp_one {X : Type} {bot : X} (ops : Fin 1 → Operator X bot) :
    opSeqComp 1 ops = ops 0 := by
  simp [opSeqComp]

theorem opSeqComp_two {X : Type} {bot : X} (ops : Fin 2 → Operator X bot) :
    opSeqComp 2 ops = opComp (ops 1) (ops 0) := by
  simp [opSeqComp]

/-- Correspondence between `opSeqComp` and Chapter 1's `OperatorChain`. -/
theorem opSeqComp_eq_operatorChain {X : Type} {bot : X}
    (k : ℕ) (ops : Fin k → Operator X bot) :
    opSeqComp k ops = OperatorChain (List.ofFn ops).reverse := by
  induction k with
  | zero =>
    ext x
    simp [OperatorChain]
  | succ k ih =>
    rw [opSeqComp_succ, List.ofFn_succ', List.concat_eq_append, List.reverse_append,
      List.reverse_singleton, List.singleton_append]
    ext x
    change (ops (Fin.last k)).func ((opSeqComp k (fun i => ops i.castSucc)).func x) =
      (ops (Fin.last k)).func ((OperatorChain (List.ofFn (fun i => ops i.castSucc)).reverse).func x)
    rw [ih]

/-- Prefix composition $c_m = \phi_m \circ \cdots \circ \phi_1$ for `m ≤ k`. -/
def prefixOpComp {X : Type} {bot : X} {k : ℕ} (ops : Fin k → Operator X bot) :
    (m : ℕ) → m ≤ k → Operator X bot
  | 0, _ => idOperator
  | m + 1, hm => opComp (ops ⟨m, hm⟩) (prefixOpComp ops m (Nat.le_of_succ_le hm))

theorem prefixOpComp_castSucc {X : Type} {bot : X} {k : ℕ}
    (ops : Fin (k + 1) → Operator X bot) (m : ℕ) (hm : m ≤ k) :
    prefixOpComp (fun i : Fin k => ops i.castSucc) m hm =
      prefixOpComp ops m (hm.trans (Nat.le_succ k)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [prefixOpComp]
    congr 1
    exact ih (Nat.le_of_succ_le hm)

theorem prefixOpComp_self {X : Type} {bot : X}
    (k : ℕ) (ops : Fin k → Operator X bot) :
    prefixOpComp ops k (le_refl k) = opSeqComp k ops := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [prefixOpComp, opSeqComp_succ, ← ih (fun m => ops m.castSucc), prefixOpComp_castSucc]
    rfl

/-- Auxiliary recursive definition of intermediate actual image domains $U_{m+1} = \phi_m(U_m)$. -/
def chainDomainAux {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) : (m : ℕ) → m ≤ k → Set X
  | 0, _ => U₀
  | m + 1, hm => operator_image (ops ⟨m, hm⟩) (chainDomainAux ops U₀ m (Nat.le_of_succ_le hm))

/-- Actual input/image domain sequence $U_0, U_1, \dots, U_k$ indexed by `Fin (k + 1)`,
where `chainDomain ops U₀ 0 = U₀` and `chainDomain ops U₀ m.succ = ops m '' chainDomain ops U₀ m.castSucc`. -/
def chainDomain {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) (m : Fin (k + 1)) : Set X :=
  chainDomainAux ops U₀ m.val (Nat.le_of_lt_succ m.isLt)

@[simp]
theorem chainDomain_zero {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) :
    chainDomain ops U₀ 0 = U₀ :=
  rfl

theorem chainDomain_succ {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) (m : Fin k) :
    chainDomain ops U₀ m.succ = operator_image (ops m) (chainDomain ops U₀ m.castSucc) := by
  rfl

theorem chainDomainAux_castSucc {X : Type} {bot : X} {k : ℕ}
    (ops : Fin (k + 1) → Operator X bot) (U₀ : Set X) (m : ℕ) (hm : m ≤ k) :
    chainDomainAux (fun i : Fin k => ops i.castSucc) U₀ m hm =
      chainDomainAux ops U₀ m (hm.trans (Nat.le_succ k)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [chainDomainAux]
    congr 1
    exact ih (Nat.le_of_succ_le hm)

theorem chainDomain_castSucc {X : Type} {bot : X} {k : ℕ}
    (ops : Fin (k + 1) → Operator X bot) (U₀ : Set X) (m : Fin (k + 1)) :
    chainDomain (fun i : Fin k => ops i.castSucc) U₀ m =
      chainDomain ops U₀ m.castSucc :=
  chainDomainAux_castSucc ops U₀ m.val (Nat.le_of_lt_succ m.isLt)

/-- Each successive domain $U_m$ equals the image of $U_0$ under the prefix composite $c_m$. -/
theorem chainDomainAux_eq_image {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) (m : ℕ) (hm : m ≤ k) :
    chainDomainAux ops U₀ m hm = operator_image (prefixOpComp ops m hm) U₀ := by
  induction m with
  | zero =>
    simp [chainDomainAux, prefixOpComp, operator_image, idOperator]
  | succ m ih =>
    simp only [chainDomainAux, prefixOpComp]
    rw [ih (Nat.le_of_succ_le hm)]
    ext y
    simp [operator_image, opComp]

/-- Full composite image equals the final successive image:
$c_k(U_0) = U_k$ (`chainDomain ops U₀ (Fin.last k)`). -/
theorem chainDomain_last_eq_image {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X) :
    chainDomain ops U₀ (Fin.last k) = operator_image (opSeqComp k ops) U₀ := by
  have hval : (Fin.last k).val = k := Fin.val_last k
  simpa [chainDomain, hval, prefixOpComp_self] using chainDomainAux_eq_image ops U₀ k (le_refl k)

theorem subset_dom_prefixOpComp_of_le {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X)
    (hdom : U₀ ⊆ dom (opSeqComp k ops)) (m : ℕ) (hm : m ≤ k) :
    U₀ ⊆ dom (prefixOpComp ops m hm) := by
  rw [← prefixOpComp_self k ops] at hdom
  have aux : ∀ n (hn : n ≤ k), U₀ ⊆ dom (prefixOpComp ops n hn) →
      ∀ r (hr : r ≤ n), U₀ ⊆ dom (prefixOpComp ops r (hr.trans hn)) := by
    intro n
    induction n with
    | zero =>
      intro hn h0 r hr
      have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
      subst hr0
      exact h0
    | succ n ih =>
      intro hn hn_dom r hr
      rcases Nat.lt_or_eq_of_le hr with hlt | heq
      · have hle : r ≤ n := Nat.lt_succ_iff.mp hlt
        have hn' : U₀ ⊆ dom (prefixOpComp ops n (Nat.le_of_succ_le hn)) :=
          (subset_dom_opComp_iff _ _ U₀).mp hn_dom |>.1
        exact ih (Nat.le_of_succ_le hn) hn' r hle
      · subst heq
        exact hn_dom
  exact aux k (le_refl k) hdom m hm

/-- Starting domain inclusion $U_0 \subseteq \mathrm{dom}(c_k)$ implies every intermediate
image domain satisfies $U_m \subseteq \mathrm{dom}(\phi_m)$. -/
theorem chainDomain_subset_dom {X : Type} {bot : X} {k : ℕ}
    (ops : Fin k → Operator X bot) (U₀ : Set X)
    (hdom : U₀ ⊆ dom (opSeqComp k ops)) (m : Fin k) :
    chainDomain ops U₀ m.castSucc ⊆ dom (ops m) := by
  have hsucc : U₀ ⊆ dom (prefixOpComp ops (m.val + 1) m.isLt) :=
    subset_dom_prefixOpComp_of_le ops U₀ hdom (m.val + 1) m.isLt
  have him : operator_image (prefixOpComp ops m.val (Nat.le_of_succ_le m.isLt)) U₀ ⊆
      dom (ops ⟨m.val, m.isLt⟩) :=
    (subset_dom_opComp_iff (ops ⟨m.val, m.isLt⟩) _ U₀).mp hsucc |>.2
  rw [← chainDomainAux_eq_image] at him
  exact him

/-! ### Lip and co-Lip matrix sets (HC02-D01, HC02-D02) -/

/-- Global Lipschitz matrix condition on $\mathrm{dom}(\phi)$. -/
def IsLipMatrix {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) : Prop :=
  ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y

/-- Set $\mathscr{L}(\phi)$ of all legal global Lipschitz matrices for $\phi$. -/
def LipSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) : Set (GaugeMatrix I) :=
  { L | IsLipMatrix d ϕ L }

/-- Restricted Lipschitz matrix condition on $U \subseteq \mathrm{dom}(\phi)$. -/
def IsRestrictedLipMatrix {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (L : GaugeMatrix I) : Prop :=
  U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    d j (ϕ.func x) (ϕ.func y) ≤ ∑ i : I, L i j * d i x y

/-- Set $\mathscr{L}(\phi)|_U$ of legal restricted Lipschitz matrices for $\phi$ on $U$. -/
def LipRestricted {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { L | IsRestrictedLipMatrix d ϕ U L }

theorem lipRestricted_dom_eq_lipSet {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) :
    LipRestricted d ϕ (dom ϕ) = LipSet d ϕ := by
  ext L
  simp [LipRestricted, IsRestrictedLipMatrix, LipSet, IsLipMatrix]

/-- Restricted co-Lipschitz matrix condition on nonempty $U \subseteq \mathrm{dom}(\phi)$.
Nonemptiness $U \neq \emptyset$ is part of the definition of $\mathscr{K}(\phi)|_U$. -/
def IsRestrictedCoLipMatrix {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (K : GaugeMatrix I) : Prop :=
  U.Nonempty ∧ U ⊆ dom ϕ ∧ ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
    (∑ i : I, K i j * d i x y) ≤ d j (ϕ.func x) (ϕ.func y)

/-- Set $\mathscr{K}(\phi)|_U$ of legal restricted co-Lipschitz matrices for $\phi$ on $U$. -/
def CoLipRestricted {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : Set (GaugeMatrix I) :=
  { K | IsRestrictedCoLipMatrix d ϕ U K }

/-- Zero coefficients are always valid in `CoLipRestricted` (when $U \neq \emptyset$ and $U \subseteq \mathrm{dom}(\phi)$). -/
theorem zero_mem_coLipRestricted {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) :
    (fun _ _ => (0 : ENNReal)) ∈ CoLipRestricted d ϕ U := by
  refine ⟨hU_ne, hU, fun _ _ _ _ _ => ?_⟩
  simp

/-- `⊤` is a legal co-Lip coefficient whenever the corresponding input distance vanishes on $U$. -/
theorem top_entry_mem_coLipRestricted_of_zero_dist {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom ϕ) (i₀ j₀ : I)
    (hzero : ∀ x ∈ U, ∀ y ∈ U, d i₀ x y = 0) :
    (fun i j => if i = i₀ ∧ j = j₀ then (⊤ : ENNReal) else 0) ∈ CoLipRestricted d ϕ U := by
  refine ⟨hU_ne, hU, fun x hx y hy j => ?_⟩
  have hsum : (∑ i : I, (if i = i₀ ∧ j = j₀ then (⊤ : ENNReal) else 0) * d i x y) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _
    by_cases h : i = i₀ ∧ j = j₀
    · rw [if_pos h, h.1, hzero x hx y hy, mul_zero]
    · rw [if_neg h, zero_mul]
  rw [hsum]
  exact zero_le _

/-- `⊤` is a legal Lip coefficient when input vanishes implies output vanishes. -/
theorem top_mem_lipRestricted_of_zero_preserving {X I : Type} {bot : X}
    [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ)
    (hpres : ∀ x ∈ U, ∀ y ∈ U, (∀ i : I, d i x y = 0) → ∀ j : I, d j (ϕ.func x) (ϕ.func y) = 0) :
    (fun _ _ => (⊤ : ENNReal)) ∈ LipRestricted d ϕ U := by
  refine ⟨hU, fun x hx y hy j => ?_⟩
  by_cases hz : ∀ i : I, d i x y = 0
  · rw [hpres x hx y hy hz j]
    exact zero_le _
  · push Not at hz
    rcases hz with ⟨i₀, hi₀⟩
    have htop : (⊤ : ENNReal) * d i₀ x y = ⊤ := ENNReal.top_mul hi₀
    have hle : (⊤ : ENNReal) * d i₀ x y ≤ ∑ i : I, (⊤ : ENNReal) * d i x y :=
      Finset.single_le_sum (f := fun i => (⊤ : ENNReal) * d i x y)
        (fun _ _ => zero_le _) (Finset.mem_univ i₀)
    rw [htop] at hle
    exact le_top.trans hle

/-! ### Single-component degeneration, domain restriction, entry infima (HC02-P01 to HC02-P04) -/

/-- **HC02-P01**: Single-component degeneration of the Lip matrix condition ($I = \{i\}$). -/
theorem lipSet_singleton_iff {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (i : I) (hI : ∀ k : I, k = i)
    (L : GaugeMatrix I) :
    L ∈ LipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ, d i (ϕ.func x) (ϕ.func y) ≤ L i i * d i x y := by
  have huniv : (Finset.univ : Finset I) = {i} := by
    ext k
    simp [hI k]
  constructor
  · intro hL x hx y hy
    have h := hL x hx y hy i
    rwa [← Finset.sum_singleton (fun k => L k i * d k x y) i, ← huniv]
  · intro h x hx y hy j
    rw [hI j, huniv, Finset.sum_singleton]
    exact h x hx y hy

theorem lipSet_unique_iff {X I : Type} {bot : X} [Fintype I] [Unique I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (L : GaugeMatrix I) :
    L ∈ LipSet d ϕ ↔
      ∀ x ∈ dom ϕ, ∀ y ∈ dom ϕ,
        d default (ϕ.func x) (ϕ.func y) ≤ L default default * d default x y :=
  lipSet_singleton_iff d ϕ default Unique.eq_default L

/-- **HC02-P02**: Global Lip certificates restrict to any subdomain $U \subseteq \mathrm{dom}(\phi)$. -/
theorem lipSet_subset_lipRestricted {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U : Set X} (hU : U ⊆ dom ϕ) :
    LipSet d ϕ ⊆ LipRestricted d ϕ U := by
  intro L hL
  exact ⟨hU, fun x hx y hy j => hL x (hU hx) y (hU hy) j⟩

/-- **HC02-P03**: Shrinking the evaluation domain enlarges the feasible Lip certificate family. -/
theorem lipRestricted_antitone {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X} (hUV : U ⊆ V) :
    LipRestricted d ϕ V ⊆ LipRestricted d ϕ U := by
  rintro L ⟨hV, hL⟩
  exact ⟨hUV.trans hV, fun x hx y hy j => hL x (hUV hx) y (hUV hy) j⟩

/-- Entrywise infimum $a_{ij}(U) = \inf \{ M_{i \to j} : M \in \mathscr{L}(\phi)|_U \}$. -/
noncomputable def lipEntryInf {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  sInf { r : ENNReal | ∃ M ∈ LipRestricted d ϕ U, M i j = r }

/-- **HC02-P04**: Entrywise infimum is non-decreasing in $U$ (non-increasing under shrinking $V$ to $U$). -/
theorem lipEntryInf_mono {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {U V : Set X} (hUV : U ⊆ V) (i j : I) :
    lipEntryInf d ϕ U i j ≤ lipEntryInf d ϕ V i j := by
  apply sInf_le_sInf
  rintro r ⟨M, hM, rfl⟩
  exact ⟨M, lipRestricted_antitone d ϕ hUV hM, rfl⟩

/-! ### Two-step composition and co-Lip vanishing criterion (HC02-P05 to HC02-P07) -/

/-- **HC02-P05**: Two-step Lip matrix composition law. -/
theorem lipRestricted_comp {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (opComp ϕ₂ ϕ₁))
    {L₁ L₂ : GaugeMatrix I}
    (hL₁ : L₁ ∈ LipRestricted d ϕ₁ U₁)
    (hL₂ : L₂ ∈ LipRestricted d ϕ₂ (operator_image ϕ₁ U₁)) :
    matMul L₂ L₁ ∈ LipRestricted d (opComp ϕ₂ ϕ₁) U₁ := by
  refine ⟨hU₁, fun x hx y hy j => ?_⟩
  have hfx : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hfy : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    d j ((opComp ϕ₂ ϕ₁).func x) ((opComp ϕ₂ ϕ₁).func y)
      = d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) := rfl
    _ ≤ ∑ k : I, L₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := hL₂.2 (ϕ₁.func x) hfx (ϕ₁.func y) hfy j
    _ ≤ ∑ k : I, L₂ k j * (∑ i : I, L₁ i k * d i x y) := by
      refine Finset.sum_le_sum ?_
      intro k _
      gcongr
      exact hL₁.2 x hx y hy k
    _ = ∑ k : I, ∑ i : I, L₂ k j * (L₁ i k * d i x y) := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [Finset.mul_sum]
    _ = ∑ i : I, ∑ k : I, (L₂ k j * L₁ i k) * d i x y := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro i _
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [mul_assoc]
    _ = ∑ i : I, matMul L₂ L₁ i j * d i x y := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [← Finset.sum_mul, matMul_apply]

/-- **HC02-P06**: Pairwise output zero distance with positive input distance forces
global co-Lip entry $K_{i \to j} = 0$. -/
theorem coLip_entry_eq_zero_of_dist_zero {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) {K : GaugeMatrix I}
    (hK : K ∈ CoLipRestricted d ϕ (dom ϕ))
    {x y : X} (hx : x ∈ dom ϕ) (hy : y ∈ dom ϕ) {i j : I}
    (hout : d j (ϕ.func x) (ϕ.func y) = 0) (hin : 0 < d i x y) :
    K i j = 0 := by
  have hsum : (∑ k : I, K k j * d k x y) ≤ 0 := by
    rw [← hout]
    exact hK.2.2 x hx y hy j
  have hsingle : K i j * d i x y ≤ 0 :=
    (Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ i)).trans hsum
  have hmul : K i j * d i x y = 0 := le_antisymm hsingle (zero_le _)
  rcases mul_eq_zero.mp hmul with h0 | h0
  · exact h0
  · exact absurd h0 (ne_of_gt hin)

/-- **HC02-P07**: Two-step co-Lip matrix composition law (preserving nonemptiness of $U_1$). -/
theorem coLipRestricted_comp {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (ϕ₁ ϕ₂ : Operator X bot)
    {U₁ : Set X} (hU₁ : U₁ ⊆ dom (opComp ϕ₂ ϕ₁))
    {K₁ K₂ : GaugeMatrix I}
    (hK₁ : K₁ ∈ CoLipRestricted d ϕ₁ U₁)
    (hK₂ : K₂ ∈ CoLipRestricted d ϕ₂ (operator_image ϕ₁ U₁)) :
    matMul K₂ K₁ ∈ CoLipRestricted d (opComp ϕ₂ ϕ₁) U₁ := by
  refine ⟨hK₁.1, hU₁, fun x hx y hy j => ?_⟩
  have hfx : ϕ₁.func x ∈ operator_image ϕ₁ U₁ := ⟨x, hx, rfl⟩
  have hfy : ϕ₁.func y ∈ operator_image ϕ₁ U₁ := ⟨y, hy, rfl⟩
  calc
    ∑ i : I, matMul K₂ K₁ i j * d i x y
      = ∑ i : I, ∑ k : I, (K₂ k j * K₁ i k) * d i x y := by
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [matMul_apply, Finset.sum_mul]
    _ = ∑ k : I, K₂ k j * (∑ i : I, K₁ i k * d i x y) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl ?_
        intro k _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [mul_assoc]
    _ ≤ ∑ k : I, K₂ k j * d k (ϕ₁.func x) (ϕ₁.func y) := by
        refine Finset.sum_le_sum ?_
        intro k _
        gcongr
        exact hK₁.2.2 x hx y hy k
    _ ≤ d j (ϕ₂.func (ϕ₁.func x)) (ϕ₂.func (ϕ₁.func y)) :=
        hK₂.2.2 (ϕ₁.func x) hfx (ϕ₁.func y) hfy j
    _ = d j ((opComp ϕ₂ ϕ₁).func x) ((opComp ϕ₂ ϕ₁).func y) := rfl

/-! ### Two-operator pairwise image distance perturbation bounds (HC02-P08 to HC02-P11) -/

/-- **HC02-P08**: Forward pairwise image distance perturbation bound. -/
theorem perturbation_dist_forward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (_hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₂.func x) (ϕ₂.func y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := by
  have hx' : d j (ϕ₂.func x) (ϕ₁.func x) ≤ δ j := by
    rw [(hd j).symm]
    exact hδ x hx j
  have hy' : d j (ϕ₁.func y) (ϕ₂.func y) ≤ δ j := hδ y hy j
  calc
    d j (ϕ₂.func x) (ϕ₂.func y)
      ≤ d j (ϕ₂.func x) (ϕ₁.func x) + d j (ϕ₁.func x) (ϕ₂.func y) := (hd j).triangle _ _ _
    _ ≤ d j (ϕ₂.func x) (ϕ₁.func x) + (d j (ϕ₁.func x) (ϕ₁.func y) + d j (ϕ₁.func y) (ϕ₂.func y)) := by
      gcongr
      exact (hd j).triangle _ _ _
    _ ≤ δ j + (d j (ϕ₁.func x) (ϕ₁.func y) + δ j) := by
      gcongr
    _ = d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := by ring

/-- **HC02-P09**: Backward pairwise image distance perturbation bound (swapping $\phi_1, \phi_2$). -/
theorem perturbation_dist_backward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₁.func x) (ϕ₁.func y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + δ j + δ j := by
  have hU' : U ⊆ commonDom₂ ϕ₂ ϕ₁ := by
    simpa [commonDom₂, Set.inter_comm] using hU
  have hδ' : ∀ z ∈ U, ∀ k : I, d k (ϕ₂.func z) (ϕ₁.func z) ≤ δ k := by
    intro z hz k
    rw [(hd k).symm]
    exact hδ z hz k
  exact perturbation_dist_forward d hd ϕ₂ ϕ₁ hU' δ hδ' hx hy j

/-- **HC02-P10**: Additive Lip upper-bound bridge from $\phi_1$ to $\phi_2$. -/
theorem perturbation_lip_bridge {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {L₁ : GaugeMatrix I} (hL₁ : L₁ ∈ LipRestricted d ϕ₁ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₂.func x) (ϕ₂.func y) ≤ (∑ i : I, L₁ i j * d i x y) + 2 * δ j := by
  have hfwd := perturbation_dist_forward d hd ϕ₁ ϕ₂ hU δ hδ hx hy j
  have hlip := hL₁.2 x hx y hy j
  calc
    d j (ϕ₂.func x) (ϕ₂.func y)
      ≤ d j (ϕ₁.func x) (ϕ₁.func y) + δ j + δ j := hfwd
    _ = d j (ϕ₁.func x) (ϕ₁.func y) + (δ j + δ j) := add_assoc _ _ _
    _ = d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j := by rw [two_mul]
    _ ≤ (∑ i : I, L₁ i j * d i x y) + 2 * δ j := by gcongr

/-- **HC02-P11**: Additive co-Lip lower-bound bridge from $\phi_1$ to $\phi_2$. -/
theorem perturbation_coLip_bridge {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {K₁ : GaugeMatrix I} (hK₁ : K₁ ∈ CoLipRestricted d ϕ₁ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    (∑ i : I, K₁ i j * d i x y) ≤ d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j := by
  have hbwd := perturbation_dist_backward d hd ϕ₁ ϕ₂ hU δ hδ hx hy j
  have hcolip := hK₁.2.2 x hx y hy j
  calc
    ∑ i : I, K₁ i j * d i x y
      ≤ d j (ϕ₁.func x) (ϕ₁.func y) := hcolip
    _ ≤ d j (ϕ₂.func x) (ϕ₂.func y) + δ j + δ j := hbwd
    _ = d j (ϕ₂.func x) (ϕ₂.func y) + 2 * δ j := by rw [add_assoc, two_mul]

/-- Swapped Lip bridge from $\phi_2$ to $\phi_1$ (remark after HC02-P11). -/
theorem perturbation_lip_bridge_symm {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {L₂ : GaugeMatrix I} (hL₂ : L₂ ∈ LipRestricted d ϕ₂ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    d j (ϕ₁.func x) (ϕ₁.func y) ≤ (∑ i : I, L₂ i j * d i x y) + 2 * δ j := by
  have hU' : U ⊆ commonDom₂ ϕ₂ ϕ₁ := by
    simpa [commonDom₂, Set.inter_comm] using hU
  have hδ' : ∀ z ∈ U, ∀ k : I, d k (ϕ₂.func z) (ϕ₁.func z) ≤ δ k := by
    intro z hz k
    rw [(hd k).symm]
    exact hδ z hz k
  exact perturbation_lip_bridge d hd ϕ₂ ϕ₁ hU' δ hδ' hL₂ hx hy j

/-- Swapped co-Lip bridge from $\phi_2$ to $\phi_1$ (remark after HC02-P11). -/
theorem perturbation_coLip_bridge_symm {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (hd : ∀ i : I, ExtendedPseudoMetric X bot (d i))
    (ϕ₁ ϕ₂ : Operator X bot) {U : Set X} (hU : U ⊆ commonDom₂ ϕ₁ ϕ₂)
    (δ : I → ENNReal) (hδ : ∀ z ∈ U, ∀ j : I, d j (ϕ₁.func z) (ϕ₂.func z) ≤ δ j)
    {K₂ : GaugeMatrix I} (hK₂ : K₂ ∈ CoLipRestricted d ϕ₂ U)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U) (j : I) :
    (∑ i : I, K₂ i j * d i x y) ≤ d j (ϕ₁.func x) (ϕ₁.func y) + 2 * δ j := by
  have hU' : U ⊆ commonDom₂ ϕ₂ ϕ₁ := by
    simpa [commonDom₂, Set.inter_comm] using hU
  have hδ' : ∀ z ∈ U, ∀ k : I, d k (ϕ₂.func z) (ϕ₁.func z) ≤ δ k := by
    intro z hz k
    rw [(hd k).symm]
    exact hδ z hz k
  exact perturbation_coLip_bridge d hd ϕ₂ ϕ₁ hU' δ hδ' hK₂ hx hy j

/-! ### Step-by-step chain structures and finite composition bounds (HC02-D05, HC02-P12 to HC02-P17) -/

/-- Step-by-step Lip certificate chain data on actual successive image domains.
Contains ONLY the step operators, initial domain `U0 ⊆ dom c_k`, step matrices,
and step validity proofs — never the composite product bound itself. -/
structure LipChainData {X I : Type} (bot : X) [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (k : ℕ) where
  ops : Fin k → Operator X bot
  U0 : Set X
  dom_subset : U0 ⊆ dom (opSeqComp k ops)
  mats : Fin k → GaugeMatrix I
  step_valid : ∀ m : Fin k, mats m ∈ LipRestricted d (ops m) (chainDomain ops U0 m.castSucc)

/-- Prefix of a `LipChainData` of length `k + 1`. -/
def lipChainPrefix {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} {k : ℕ} (chain : LipChainData bot d (k + 1)) :
    LipChainData bot d k where
  ops := fun m => chain.ops m.castSucc
  U0 := chain.U0
  dom_subset := (subset_dom_opComp_iff _ _ chain.U0).mp chain.dom_subset |>.1
  mats := fun m => chain.mats m.castSucc
  step_valid := fun m => by
    rw [chainDomain_castSucc]
    exact chain.step_valid m.castSucc

/-- Step-by-step co-Lip certificate chain data on actual successive image domains.
Contains ONLY the step operators, initial domain `U0 ⊆ dom c_k`, step matrices,
and step validity proofs — never the composite product bound itself. -/
structure CoLipChainData {X I : Type} (bot : X) [Fintype I] [Nonempty I]
    (d : I → X → X → ENNReal) (k : ℕ) where
  ops : Fin k → Operator X bot
  U0 : Set X
  dom_subset : U0 ⊆ dom (opSeqComp k ops)
  mats : Fin k → GaugeMatrix I
  step_valid : ∀ m : Fin k, mats m ∈ CoLipRestricted d (ops m) (chainDomain ops U0 m.castSucc)

/-- Prefix of a `CoLipChainData` of length `k + 1`. -/
def coLipChainPrefix {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} {k : ℕ} (chain : CoLipChainData bot d (k + 1)) :
    CoLipChainData bot d k where
  ops := fun m => chain.ops m.castSucc
  U0 := chain.U0
  dom_subset := (subset_dom_opComp_iff _ _ chain.U0).mp chain.dom_subset |>.1
  mats := fun m => chain.mats m.castSucc
  step_valid := fun m => by
    rw [chainDomain_castSucc]
    exact chain.step_valid m.castSucc

/-- Every actual domain `chainDomain chain.ops chain.U0 m` along a non-empty co-Lip chain
(`k ≥ 1`) is nonempty. -/
theorem coLipChain_domains_nonempty {X I : Type} {bot : X} [Fintype I] [Nonempty I]
    {d : I → X → X → ENNReal} {k : ℕ} (hk : 1 ≤ k) (chain : CoLipChainData bot d k)
    (m : Fin (k + 1)) :
    (chainDomain chain.ops chain.U0 m).Nonempty := by
  have h0 : chain.U0.Nonempty := (chain.step_valid ⟨0, hk⟩).1
  rcases h0 with ⟨x₀, hx₀⟩
  rw [chainDomain, chainDomainAux_eq_image]
  exact ⟨(prefixOpComp chain.ops m.val (Nat.le_of_lt_succ m.isLt)).func x₀, x₀, hx₀, rfl⟩

/-- **HC02-P14 (helper)**: Identity matrix is a legal Lip matrix on any `U ⊆ dom idOperator`. -/
theorem idMatrix_mem_lipRestricted {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X} (hU : U ⊆ dom (idOperator (X := X) (bot := bot))) :
    idMatrix ∈ LipRestricted d (idOperator (X := X) (bot := bot)) U := by
  refine ⟨hU, fun x _ y _ j => ?_⟩
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [idMatrix_apply_ne hij]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/-- **HC02-P14**: Zero-step composition ($k = 0$, $c_0 = \mathrm{id}$) admits `idMatrix`
as a legal Lip matrix on any nonempty $U \subseteq \mathrm{dom}(\mathrm{id})$. -/
theorem zero_step_idMatrix_mem_lipRestricted {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ops : Fin 0 → Operator X bot)
    (mats : Fin 0 → GaugeMatrix I) {U : Set X}
    (_hU_ne : U.Nonempty) (hU : U ⊆ dom (opSeqComp 0 ops)) :
    matProd 0 mats ∈ LipRestricted d (opSeqComp 0 ops) U := by
  simpa [matProd_zero, opSeqComp_zero] using idMatrix_mem_lipRestricted d hU

/-- **HC02-P15**: Zero-step composition ($k = 0$, $c_0 = \mathrm{id}$) admits `idMatrix`
as a legal co-Lip matrix on any nonempty $U \subseteq \mathrm{dom}(\mathrm{id})$. -/
theorem idMatrix_mem_coLipRestricted {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom (idOperator (X := X) (bot := bot))) :
    idMatrix ∈ CoLipRestricted d (idOperator (X := X) (bot := bot)) U := by
  refine ⟨hU_ne, hU, fun x _ y _ j => ?_⟩
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    simp [idMatrix_apply_ne hij]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem zero_step_idMatrix_mem_coLipRestricted {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) (ops : Fin 0 → Operator X bot)
    (mats : Fin 0 → GaugeMatrix I) {U : Set X}
    (hU_ne : U.Nonempty) (hU : U ⊆ dom (opSeqComp 0 ops)) :
    matProd 0 mats ∈ CoLipRestricted d (opSeqComp 0 ops) U := by
  simpa [matProd_zero, opSeqComp_zero] using idMatrix_mem_coLipRestricted d hU_ne hU

/-- **HC02-P12 (all $k$)**: Finite composition local Lip matrix bound for all $k \in \mathbb{N}$. -/
theorem lipChain_prod_mem_all {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) :
    ∀ (k : ℕ) (chain : LipChainData bot d k),
      matProd k chain.mats ∈ LipRestricted d (opSeqComp k chain.ops) chain.U0
  | 0, chain => idMatrix_mem_lipRestricted d chain.dom_subset
  | k + 1, chain => by
    have hpre := lipChain_prod_mem_all d k (lipChainPrefix chain)
    have hlast := chain.step_valid (Fin.last k)
    have him : chainDomain chain.ops chain.U0 (Fin.last k).castSucc =
        operator_image (opSeqComp k (lipChainPrefix chain).ops) chain.U0 := by
      rw [← chainDomain_castSucc]
      exact chainDomain_last_eq_image (lipChainPrefix chain).ops chain.U0
    rw [him] at hlast
    rw [matProd_succ, opSeqComp_succ]
    exact lipRestricted_comp d _ _ chain.dom_subset hpre hlast

/-- **HC02-P12**: Finite composition local Lip matrix bound for any positive chain length $k \ge 1$. -/
theorem lipChain_prod_mem {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) {k : ℕ} (_hk : 1 ≤ k) (chain : LipChainData bot d k) :
    matProd k chain.mats ∈ LipRestricted d (opSeqComp k chain.ops) chain.U0 :=
  lipChain_prod_mem_all d k chain

/-- **HC02-P13 (helper for `k = k' + 1`)**: Finite composition local co-Lip matrix bound. -/
theorem coLipChain_succ_prod_mem {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) :
    ∀ (k' : ℕ) (chain : CoLipChainData bot d (k' + 1)),
      matProd (k' + 1) chain.mats ∈ CoLipRestricted d (opSeqComp (k' + 1) chain.ops) chain.U0
  | 0, chain => by
    simpa [matProd_one, opSeqComp_one] using chain.step_valid 0
  | k' + 1, chain => by
    have hpre := coLipChain_succ_prod_mem d k' (coLipChainPrefix chain)
    have hlast := chain.step_valid (Fin.last (k' + 1))
    have him : chainDomain chain.ops chain.U0 (Fin.last (k' + 1)).castSucc =
        operator_image (opSeqComp (k' + 1) (coLipChainPrefix chain).ops) chain.U0 := by
      rw [← chainDomain_castSucc]
      exact chainDomain_last_eq_image (coLipChainPrefix chain).ops chain.U0
    rw [him] at hlast
    rw [matProd_succ, opSeqComp_succ]
    exact coLipRestricted_comp d _ _ chain.dom_subset hpre hlast

/-- **HC02-P13**: Finite composition local co-Lip matrix bound for any positive chain length $k \ge 1$. -/
theorem coLipChain_prod_mem {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    (d : I → X → X → ENNReal) {k : ℕ} (hk : 1 ≤ k) (chain : CoLipChainData bot d k) :
    matProd k chain.mats ∈ CoLipRestricted d (opSeqComp k chain.ops) chain.U0 := by
  cases k with
  | zero => exact absurd hk (by omega)
  | succ k' => exact coLipChain_succ_prod_mem d k' chain

/-- Pure matrix entry zero criterion over all finite index paths ($n \ge 1$). -/
theorem matProd_eq_zero_iff_all_paths_hasZero {I : Type} [Fintype I] [DecidableEq I]
    {n : ℕ} (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    matProd n M i j = 0 ↔ ∀ mid : Fin (n - 1) → I, PathHasZero M i j mid := by
  rw [matProd_apply_eq_sum_paths hn M i j, Finset.sum_eq_zero_iff]
  refine ⟨fun h mid => ?_, fun h mid _ => ?_⟩
  · exact (pathWeight_eq_zero_iff M i j mid).mp (h mid (Finset.mem_univ mid))
  · exact (pathWeight_eq_zero_iff M i j mid).mpr (h mid)

/-- Pure matrix entry positivity criterion over finite index paths ($n \ge 1$). -/
theorem matProd_pos_iff_exists_path_allPos {I : Type} [Fintype I] [DecidableEq I]
    {n : ℕ} (hn : 1 ≤ n) (M : Fin n → GaugeMatrix I) (i j : I) :
    0 < matProd n M i j ↔ ∃ mid : Fin (n - 1) → I, PathAllPos M i j mid := by
  rw [matProd_apply_eq_sum_paths hn M i j, pos_iff_ne_zero, ne_eq, Finset.sum_eq_zero_iff]
  push Not
  constructor
  · rintro ⟨mid, _, hne⟩
    exact ⟨mid, (pathWeight_pos_iff M i j mid).mp (pos_iff_ne_zero.mpr hne)⟩
  · rintro ⟨mid, hpos⟩
    exact ⟨mid, Finset.mem_univ mid, ne_of_gt ((pathWeight_pos_iff M i j mid).mpr hpos)⟩

/-- **HC02-P16**: Along a Lip certificate chain of length $n \ge 1$, the product entry $(i \to j)$
vanishes if and only if every intermediate index path contains at least one zero entry. -/
theorem lipChain_prod_eq_zero_iff {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    {d : I → X → X → ENNReal} {n : ℕ} (hn : 1 ≤ n) (chain : LipChainData bot d n) (i j : I) :
    matProd n chain.mats i j = 0 ↔ ∀ mid : Fin (n - 1) → I, PathHasZero chain.mats i j mid :=
  matProd_eq_zero_iff_all_paths_hasZero hn chain.mats i j

/-- **HC02-P16 ($n = 1$ degeneration)**: At $n = 1$, the zero criterion reduces to $L^{(1)}_{i \to j} = 0$. -/
theorem lipChain_prod_one_eq_zero_iff {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    {d : I → X → X → ENNReal} (chain : LipChainData bot d 1) (i j : I) :
    (∀ mid : Fin 0 → I, PathHasZero chain.mats i j mid) ↔ chain.mats 0 i j = 0 := by
  constructor
  · intro h
    exact (pathHasZero_one_iff chain.mats i j Fin.elim0).mp (h Fin.elim0)
  · intro h mid
    exact (pathHasZero_one_iff chain.mats i j mid).mpr h

/-- **HC02-P17**: Along a co-Lip certificate chain of length $n \ge 1$, the product entry $(i \to j)$
is strictly positive if and only if there exists an intermediate index path with all edges positive. -/
theorem coLipChain_prod_pos_iff {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    {d : I → X → X → ENNReal} {n : ℕ} (hn : 1 ≤ n) (chain : CoLipChainData bot d n) (i j : I) :
    0 < matProd n chain.mats i j ↔ ∃ mid : Fin (n - 1) → I, PathAllPos chain.mats i j mid :=
  matProd_pos_iff_exists_path_allPos hn chain.mats i j

/-- **HC02-P17 ($n = 1$ degeneration)**: At $n = 1$, the unique empty intermediate sequence gives $K^{(1)}_{i \to j} > 0$. -/
theorem coLipChain_prod_one_pos_iff {X I : Type} {bot : X}
    [Fintype I] [Nonempty I] [DecidableEq I]
    {d : I → X → X → ENNReal} (chain : CoLipChainData bot d 1) (i j : I) :
    (∃ mid : Fin 0 → I, PathAllPos chain.mats i j mid) ↔ 0 < chain.mats 0 i j := by
  constructor
  · rintro ⟨mid, h⟩
    exact (pathAllPos_one_iff chain.mats i j mid).mp h
  · intro h
    exact ⟨Fin.elim0, (pathAllPos_one_iff chain.mats i j Fin.elim0).mpr h⟩

end formal_oet.vol_01.ch_02_operator_bounds
