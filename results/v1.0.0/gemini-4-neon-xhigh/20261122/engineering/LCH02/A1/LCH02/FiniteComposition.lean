/-
Attribution: Formalization of material from Zhe Li (Glen Li / glenzli),
ORCID https://orcid.org/0009-0006-6536-3453,
The Operator Evolution Theory, Volume I, v1.0.0, https://glenzli.com/books/oet/,
licensed under CC BY 4.0.
-/
import formal_oet.vol_01.ch_01_foundations.operator_space
import LCH02.GaugeMatrix
import LCH02.LipBounds

namespace LCH02

open formal_oet.vol_01.ch_01_foundations

/--
Finite composition `c_k = ϕ_k ∘ ... ∘ ϕ_1` of operators given in chronological step order
`ϕs : Fin k → Operator X bot` (where `ϕs 0 = ϕ_1` acts first and `ϕs (Fin.last _) = ϕ_k` acts last).
For `k = 0`, `c_0 = id_X = operator_identity`.
-/
def chainCompose {X : Type} {bot : X} :
    {k : Nat} → (Fin k → Operator X bot) → Operator X bot
  | 0, _ => operator_identity
  | _ + 1, ϕs => ϕs (Fin.last _) * chainCompose (fun m => ϕs m.castSucc)

@[simp] theorem chainCompose_zero {X : Type} {bot : X} (ϕs : Fin 0 → Operator X bot) :
    chainCompose ϕs = operator_identity :=
  rfl

@[simp] theorem chainCompose_one {X : Type} {bot : X} (ϕs : Fin 1 → Operator X bot) :
    chainCompose ϕs = ϕs 0 := by
  change ϕs 0 * operator_identity = ϕs 0
  exact mul_one (ϕs 0)

theorem chainCompose_succ {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin (k + 1) → Operator X bot) :
    chainCompose ϕs = ϕs (Fin.last k) * chainCompose (fun m => ϕs m.castSucc) :=
  rfl

theorem chainCompose_eq_listProd {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) :
    chainCompose ϕs = (List.ofFn ϕs).reverse.prod := by
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      rw [chainCompose_succ, List.ofFn_succ', List.concat_eq_append]
      simp [ih (fun m => ϕs m.castSucc)]

/--
Chain representation correspondence (forward):
the chronological composition `c_k = ϕ_k ∘ ... ∘ ϕ_1` coincides with the frozen prerequisite
`OperatorChain` applied to the reversed (outermost-first) list `[ϕ_k, ..., ϕ_1]`.
-/
theorem chainCompose_eq_operatorChain_reverse {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) :
    chainCompose ϕs = OperatorChain (List.ofFn ϕs).reverse := by
  rw [chainCompose_eq_listProd, operator_chain_eq_prod]

/--
Extract chronological step operators `(ϕ_1, ..., ϕ_k)` from an outermost-first list
`ops = [ϕ_k, ..., ϕ_1]` as used by `OperatorChain`.
-/
def stepsOfOperatorChain {X : Type} {bot : X} (ops : List (Operator X bot)) :
    Fin ops.length → Operator X bot :=
  fun m => ops.reverse[m.val]'(by simp [m.isLt])

theorem list_ofFn_stepsOfOperatorChain {X : Type} {bot : X} (ops : List (Operator X bot)) :
    List.ofFn (stepsOfOperatorChain ops) = ops.reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp [stepsOfOperatorChain]

/--
Chain representation correspondence (backward):
every `OperatorChain ops` equals `chainCompose (stepsOfOperatorChain ops)`.
-/
theorem operatorChain_eq_chainCompose {X : Type} {bot : X}
    (ops : List (Operator X bot)) :
    OperatorChain ops = chainCompose (stepsOfOperatorChain ops) := by
  rw [chainCompose_eq_operatorChain_reverse, list_ofFn_stepsOfOperatorChain, List.reverse_reverse]

/--
Actual intermediate image domains `U_1, U_2, ..., U_{k+1}` along a finite operator chain:
- `intermediateDomain ϕs U₁ 0 = U₁`
- `intermediateDomain ϕs U₁ (m + 1) = ϕ_m(U_m)` (`operator_image (ϕs m) (U_m)`).
Index `m.castSucc` is the actual input domain `U_m` of step `m`.
-/
def intermediateDomain {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) : Fin (k + 1) → Set X :=
  Fin.induction U₁ (fun m Um => operator_image (ϕs m) Um)

@[simp] theorem intermediateDomain_zero {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) :
    intermediateDomain ϕs U₁ 0 = U₁ :=
  Fin.induction_zero _ _

theorem intermediateDomain_succ {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) (m : Fin k) :
    intermediateDomain ϕs U₁ m.succ =
      operator_image (ϕs m) (intermediateDomain ϕs U₁ m.castSucc) :=
  Fin.induction_succ _ _ m

/-- Intermediate domains of a prefix chain match the initial segment of the full chain. -/
theorem intermediateDomain_prefix {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin (k + 1) → Operator X bot) (U₁ : Set X) (t : Fin (k + 1)) :
    intermediateDomain (fun m : Fin k => ϕs m.castSucc) U₁ t =
      intermediateDomain ϕs U₁ t.castSucc := by
  refine Fin.induction ?_ ?_ t
  · simp [intermediateDomain_zero]
  · intro m ih
    have hsucc : m.succ.castSucc = m.castSucc.succ := by
      ext
      simp
    rw [intermediateDomain_succ, hsucc, intermediateDomain_succ, ih]

theorem operator_image_identity {X : Type} {bot : X} (U : Set X) :
    operator_image (operator_identity (X := X) (bot := bot)) U = U := by
  ext x
  simp [operator_image, operator_identity]

theorem operator_image_mul {X : Type} {bot : X}
    (ϕ₁ ϕ₂ : Operator X bot) (U : Set X) :
    operator_image (ϕ₂ * ϕ₁) U = operator_image ϕ₂ (operator_image ϕ₁ U) := by
  ext z
  simp [operator_image]
  rfl

/-- The final intermediate image domain `U_{k+1}` equals the image of `U₁` under `c_k`. -/
theorem intermediateDomain_last {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) (U₁ : Set X) :
    intermediateDomain ϕs U₁ (Fin.last k) = operator_image (chainCompose ϕs) U₁ := by
  induction k with
  | zero =>
      simp [intermediateDomain_zero, chainCompose_zero, operator_image_identity]
  | succ k ih =>
      have hlast : Fin.last (k + 1) = (Fin.last k).succ := by
        ext
        simp
      rw [hlast, intermediateDomain_succ, ← intermediateDomain_prefix,
        ih (fun m => ϕs m.castSucc), chainCompose_succ, operator_image_mul]

/--
Domain propagation along a finite chain (proof step of Corollary 2.5):
if `U₁ ⊆ dom c_k`, then every actual intermediate domain satisfies `U_m ⊆ dom ϕ_m`.
-/
theorem intermediateDomain_subset_dom {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs)) :
    ∀ m : Fin k, intermediateDomain ϕs U₁ m.castSucc ⊆ dom (ϕs m) := by
  induction k with
  | zero =>
      intro m
      exact Fin.elim0 m
  | succ k ih =>
      rw [chainCompose_succ, subset_dom_mul_iff] at hU₁
      rcases hU₁ with ⟨hU₁_init, hU_last⟩
      intro m
      refine Fin.lastCases ?_ ?_ m
      · rw [← intermediateDomain_prefix, intermediateDomain_last]
        exact hU_last
      · intro m'
        rw [← intermediateDomain_prefix]
        exact ih (fun i => ϕs i.castSucc) hU₁_init m'

/-- Nonemptiness propagation: if `U₁` is nonempty, every intermediate domain `U_m` is nonempty. -/
theorem intermediateDomain_nonempty {X : Type} {bot : X} {k : Nat}
    (ϕs : Fin k → Operator X bot) {U₁ : Set X} (hU₁ : U₁.Nonempty) :
    ∀ t : Fin (k + 1), (intermediateDomain ϕs U₁ t).Nonempty := by
  intro t
  refine Fin.induction ?_ ?_ t
  · simpa [intermediateDomain_zero] using hU₁
  · intro m ih
    rw [intermediateDomain_succ]
    exact operator_image_nonempty (ϕs m) ih

/--
**Corollary 2.5 (i) (Local Lip matrix bound for finite composition, `k + 1 ≥ 1`)**:
For any positive-length chain `c_{k+1} = ϕ_{k+1} ∘ ... ∘ ϕ_1` and `U₁ ⊆ dom c_{k+1}`,
if each step `m` has a local Lip certificate `L^(m) ∈ ℒ(ϕ_m)|_{U_m}` on the actual
intermediate domain `U_m`, then the ordered product `L^(k+1) · ... · L^(1)` lies in
`ℒ(c_{k+1})|_{U₁}`.
-/
theorem chain_restrictedLipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {k : Nat}
    (ϕs : Fin (k + 1) → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs))
    (Ls : Fin (k + 1) → GaugeMatrix I)
    (hLs : ∀ m : Fin (k + 1),
      Ls m ∈ RestrictedLipFamily d (ϕs m) (intermediateDomain ϕs U₁ m.castSucc)) :
    orderedMatrixProdNonempty Ls ∈ RestrictedLipFamily d (chainCompose ϕs) U₁ := by
  induction k with
  | zero =>
      have h0 := hLs 0
      simpa [chainCompose_one, orderedMatrixProdNonempty_zero, intermediateDomain_zero] using h0
  | succ k ih =>
      let ϕs_init : Fin (k + 1) → Operator X bot := fun m => ϕs m.castSucc
      let Ls_init : Fin (k + 1) → GaugeMatrix I := fun m => Ls m.castSucc
      have hU₁_split : U₁ ⊆ dom (ϕs (Fin.last (k + 1)) * chainCompose ϕs_init) := hU₁
      have hU₁_init : U₁ ⊆ dom (chainCompose ϕs_init) :=
        (subset_dom_mul_iff (chainCompose ϕs_init) (ϕs (Fin.last (k + 1))) U₁).mp hU₁_split |>.1
      have hLs_init : ∀ m : Fin (k + 1),
          Ls_init m ∈ RestrictedLipFamily d (ϕs_init m) (intermediateDomain ϕs_init U₁ m.castSucc) := by
        intro m
        rw [intermediateDomain_prefix]
        exact hLs m.castSucc
      have h_init := ih ϕs_init hU₁_init Ls_init hLs_init
      have h_last : Ls (Fin.last (k + 1)) ∈
          RestrictedLipFamily d (ϕs (Fin.last (k + 1)))
            (operator_image (chainCompose ϕs_init) U₁) := by
        have h := hLs (Fin.last (k + 1))
        rw [← intermediateDomain_prefix, intermediateDomain_last] at h
        exact h
      rw [chainCompose_succ, orderedMatrixProdNonempty_succ]
      exact restrictedLipFamily_comp d (chainCompose ϕs_init) (ϕs (Fin.last (k + 1)))
        hU₁_split h_init h_last

/--
Corollary 2.5 (i) stated for `orderedMatrixProd` at any positive length `1 ≤ k`.
-/
theorem chain_restrictedLipFamily_of_pos {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {k : Nat} (hk : 1 ≤ k)
    (ϕs : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs))
    (Ls : Fin k → GaugeMatrix I)
    (hLs : ∀ m : Fin k,
      Ls m ∈ RestrictedLipFamily d (ϕs m) (intermediateDomain ϕs U₁ m.castSucc)) :
    orderedMatrixProd Ls ∈ RestrictedLipFamily d (chainCompose ϕs) U₁ := by
  cases k with
  | zero =>
      omega
  | succ k' =>
      exact chain_restrictedLipFamily d ϕs hU₁ Ls hLs

/--
**Corollary 2.5 (ii) (Local co-Lip matrix bound for finite composition, `k + 1 ≥ 1`)**:
For any positive-length chain `c_{k+1} = ϕ_{k+1} ∘ ... ∘ ϕ_1` and `U₁ ⊆ dom c_{k+1}`,
if each step `m` has a local co-Lip certificate `K^(m) ∈ 𝒦(ϕ_m)|_{U_m}` on the actual
intermediate domain `U_m`, then the ordered product `K^(k+1) · ... · K^(1)` lies in
`𝒦(c_{k+1})|_{U₁}`.
-/
theorem chain_restrictedCoLipFamily {X I : Type} {bot : X} [Fintype I]
    (d : I → X → X → ENNReal) {k : Nat}
    (ϕs : Fin (k + 1) → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs))
    (Ks : Fin (k + 1) → GaugeMatrix I)
    (hKs : ∀ m : Fin (k + 1),
      Ks m ∈ RestrictedCoLipFamily d (ϕs m) (intermediateDomain ϕs U₁ m.castSucc)) :
    orderedMatrixProdNonempty Ks ∈ RestrictedCoLipFamily d (chainCompose ϕs) U₁ := by
  induction k with
  | zero =>
      have h0 := hKs 0
      simpa [chainCompose_one, orderedMatrixProdNonempty_zero, intermediateDomain_zero] using h0
  | succ k ih =>
      let ϕs_init : Fin (k + 1) → Operator X bot := fun m => ϕs m.castSucc
      let Ks_init : Fin (k + 1) → GaugeMatrix I := fun m => Ks m.castSucc
      have hU₁_split : U₁ ⊆ dom (ϕs (Fin.last (k + 1)) * chainCompose ϕs_init) := hU₁
      have hU₁_init : U₁ ⊆ dom (chainCompose ϕs_init) :=
        (subset_dom_mul_iff (chainCompose ϕs_init) (ϕs (Fin.last (k + 1))) U₁).mp hU₁_split |>.1
      have hKs_init : ∀ m : Fin (k + 1),
          Ks_init m ∈
            RestrictedCoLipFamily d (ϕs_init m) (intermediateDomain ϕs_init U₁ m.castSucc) := by
        intro m
        rw [intermediateDomain_prefix]
        exact hKs m.castSucc
      have h_init := ih ϕs_init hU₁_init Ks_init hKs_init
      have h_last : Ks (Fin.last (k + 1)) ∈
          RestrictedCoLipFamily d (ϕs (Fin.last (k + 1)))
            (operator_image (chainCompose ϕs_init) U₁) := by
        have h := hKs (Fin.last (k + 1))
        rw [← intermediateDomain_prefix, intermediateDomain_last] at h
        exact h
      rw [chainCompose_succ, orderedMatrixProdNonempty_succ]
      exact restrictedCoLipFamily_comp d (chainCompose ϕs_init) (ϕs (Fin.last (k + 1)))
        hU₁_split h_init h_last

/--
Corollary 2.5 (ii) stated for `orderedMatrixProd` at any positive length `1 ≤ k`.
-/
theorem chain_restrictedCoLipFamily_of_pos {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal) {k : Nat} (hk : 1 ≤ k)
    (ϕs : Fin k → Operator X bot) {U₁ : Set X}
    (hU₁ : U₁ ⊆ dom (chainCompose ϕs))
    (Ks : Fin k → GaugeMatrix I)
    (hKs : ∀ m : Fin k,
      Ks m ∈ RestrictedCoLipFamily d (ϕs m) (intermediateDomain ϕs U₁ m.castSucc)) :
    orderedMatrixProd Ks ∈ RestrictedCoLipFamily d (chainCompose ϕs) U₁ := by
  cases k with
  | zero =>
      omega
  | succ k' =>
      exact chain_restrictedCoLipFamily d ϕs hU₁ Ks hKs

/--
**Remark (Zero-step boundary `k = 0`, Lip certificate)**:
For the empty chain `c_0 = id_X` and empty matrix product `I`,
`orderedMatrixProd Ls ∈ ℒ(c_0)|_U` for every `U ⊆ dom c_0`.
-/
theorem zeroStep_chain_restrictedLipFamily {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal)
    (ϕs : Fin 0 → Operator X bot) (Ls : Fin 0 → GaugeMatrix I)
    {U : Set X} (hU : U ⊆ dom (chainCompose ϕs)) :
    orderedMatrixProd Ls ∈ RestrictedLipFamily d (chainCompose ϕs) U := by
  simpa [chainCompose_zero, orderedMatrixProd_zero] using
    idMatrix_mem_restrictedLipFamily_identity d hU

/--
**Remark (Zero-step boundary `k = 0`, co-Lip certificate)**:
For the empty chain `c_0 = id_X` and empty matrix product `I`,
`orderedMatrixProd Ks ∈ 𝒦(c_0)|_U` for every nonempty `U ⊆ dom c_0`.
-/
theorem zeroStep_chain_restrictedCoLipFamily {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
    (d : I → X → X → ENNReal)
    (ϕs : Fin 0 → Operator X bot) (Ks : Fin 0 → GaugeMatrix I)
    {U : Set X} (hU_ne : U.Nonempty) (hU : U ⊆ dom (chainCompose ϕs)) :
    orderedMatrixProd Ks ∈ RestrictedCoLipFamily d (chainCompose ϕs) U := by
  simpa [chainCompose_zero, orderedMatrixProd_zero] using
    idMatrix_mem_restrictedCoLipFamily_identity d hU_ne hU

end LCH02
