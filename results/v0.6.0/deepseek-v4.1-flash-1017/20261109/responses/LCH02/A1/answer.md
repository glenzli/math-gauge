LCH02 已完成：20 项义务全部标记为 `complete`。源码通过 `lake build`，关键声明经 `#print axioms` 检查仅依赖 `propext`、`Classical.choice`、`Quot.sound`；未使用 `sorry`、`admit` 或新增公理，未修改 `formal_oet/`。

```lean filename=OET/Chapter02/Matrix.lean
import Mathlib
import formal_oet.vol_01.ch_01_foundations.operator_space

/-!
# Chapter 2: finite extended nonnegative matrices and paths

This file formalizes the matrix-indexing convention used throughout Chapter 2
of the source text, the ordered finite product of such matrices, and the
positive/zero path criteria (Proposition 2.6).

An entry `M i j` always has `i` as the input component (column) and `j` as the
output component (row).  Thus composition `φ₂ ∘ φ₁` uses the product
`matMul L₂ L₁`, whose entry is `∑ k, L₂ k j * L₁ i k`.
-/

namespace OET.Chapter02

open formal_oet.vol_01.ch_01_foundations

universe u

noncomputable section

/-- Extended nonnegative matrices indexed by a finite component set.
`M i j` is the coefficient from input component `i` to output component `j`. -/
abbrev Mat (I : Type) := I → I → ENNReal

/-- The identity matrix with respect to the input/output convention. -/
def matId {I : Type} [DecidableEq I] : Mat I :=
  fun i j => if i = j then 1 else 0

@[simp]
theorem matId_apply {I : Type} [DecidableEq I] (i j : I) :
    matId i j = if i = j then 1 else 0 := rfl

/-- Matrix multiplication in source convention:
`(M₂ · M₁) i j = ∑ k, M₂ k j * M₁ i k`. -/
def matMul {I : Type} [Fintype I] (M₂ M₁ : Mat I) : Mat I :=
  fun i j => ∑ k, M₂ k j * M₁ i k

@[simp]
theorem matMul_apply {I : Type} [Fintype I] (M₂ M₁ : Mat I) (i j : I) :
    matMul M₂ M₁ i j = ∑ k, M₂ k j * M₁ i k := rfl

theorem matMul_matId {I : Type} [Fintype I] [DecidableEq I] (M : Mat I) :
    matMul M matId = M := by
  funext i j
  rw [matMul_apply, Finset.sum_eq_single i]
  · simp [matId]
  · intro k _ hki
    simp [matId, Ne.symm hki]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

theorem matId_matMul {I : Type} [Fintype I] [DecidableEq I] (M : Mat I) :
    matMul matId M = M := by
  funext i j
  rw [matMul_apply, Finset.sum_eq_single j]
  · simp [matId]
  · intro k _ hkj
    simp [matId, hkj]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/-- Associativity of the source-convention matrix product. -/
theorem matMul_assoc {I : Type} [Fintype I] (A B C : Mat I) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i j
  simp only [matMul_apply]
  calc
    (∑ k, (∑ l, A l j * B k l) * C i k)
        = ∑ k, ∑ l, A l j * B k l * C i k := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.sum_mul]
    _ = ∑ l, ∑ k, A l j * B k l * C i k := Finset.sum_comm
    _ = ∑ l, A l j * ∑ k, B k l * C i k := by
            apply Finset.sum_congr rfl
            intro l _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring

/-- Ordered product of a finite nonempty family of matrices.

The recurrence multiplies the last matrix on the outside and the prefix on the
inside.  Thus for `M : Fin n → Mat I`,
`orderedMatProd M = M (n-1) · ... · M 0`, exactly the product needed for a
chain whose zeroth step acts first.  The empty case is `matId`. -/
def orderedMatProd {I : Type} [Fintype I] [DecidableEq I] :
    {n : ℕ} → (Fin n → Mat I) → Mat I
  | 0, _ => matId
  | n + 1, M => matMul (M (Fin.last n)) (orderedMatProd (fun k => M k.castSucc))

@[simp]
theorem orderedMatProd_zero {I : Type} [Fintype I] [DecidableEq I]
    (M : Fin 0 → Mat I) :
    orderedMatProd M = matId := rfl

theorem orderedMatProd_succ {I : Type} [Fintype I] [DecidableEq I]
    {n : ℕ} (M : Fin (n + 1) → Mat I) :
    orderedMatProd M =
      matMul (M (Fin.last n)) (orderedMatProd (fun k : Fin n => M k.castSucc)) :=
  rfl

/-- The one-step ordered product is the original matrix. -/
theorem orderedMatProd_one {I : Type} [Fintype I] [DecidableEq I]
    (M : Mat I) :
    orderedMatProd (fun _ : Fin 1 => M) = M := by
  rw [orderedMatProd_succ, orderedMatProd_zero, matMul_matId]

/-- A path of length `n` from `i` to `j`, represented by its `n + 1` vertices.
This is the path object used in Proposition 2.6. -/
structure Path (I : Type) (n : ℕ) (i j : I) where
  vertex : Fin (n + 1) → I
  start : vertex 0 = i
  finish : vertex (Fin.last n) = j

namespace Path

/-- Extend a path by one final vertex. -/
def snoc {I : Type} {n : ℕ} {i j : I} (p : Path I n i j) (k : I) :
    Path I (n + 1) i k where
  vertex := Fin.snoc p.vertex k
  start := by
    simpa [Fin.snoc_castSucc] using p.start
  finish := by
    simp

/-- Remove the last vertex of a path. -/
def prePath {I : Type} {n : ℕ} {i j : I} (p : Path I (n + 1) i j) :
    Path I n i (p.vertex (Fin.castSucc (Fin.last n))) where
  vertex m := p.vertex m.castSucc
  start := p.start
  finish := rfl

/-- The penultimate vertex of a positive-length path. -/
def lastVertex {I : Type} {n : ℕ} {i j : I} (p : Path I (n + 1) i j) : I :=
  p.vertex (Fin.castSucc (Fin.last n))

@[simp]
lemma snoc_vertex_castSucc {I : Type} {n : ℕ} {i j : I}
    (p : Path I n i j) (k : I) (m : Fin (n + 1)) :
    (p.snoc k).vertex m.castSucc = p.vertex m := by
  simp [snoc, Fin.snoc_castSucc]

@[simp]
lemma snoc_vertex_last {I : Type} {n : ℕ} {i j : I}
    (p : Path I n i j) (k : I) :
    (p.snoc k).vertex (Fin.last (n + 1)) = k := by
  simp [snoc]

end Path

/-- A path is all-positive when every one of its matrix entries is strictly
positive. -/
def IsPositivePath {I : Type} {n : ℕ} {i j : I}
    (M : Fin n → Mat I) (p : Path I n i j) : Prop :=
  ∀ m : Fin n, 0 < M m (p.vertex m.castSucc) (p.vertex m.succ)

/-- A path has a zero when at least one of its matrix entries is zero. -/
def PathHasZero {I : Type} {n : ℕ} {i j : I}
    (M : Fin n → Mat I) (p : Path I n i j) : Prop :=
  ∃ m : Fin n, M m (p.vertex m.castSucc) (p.vertex m.succ) = 0

lemma snoc_edge_castSucc {I : Type} {n : ℕ} {i j : I}
    (p : Path I n i j) (k : I) (m : Fin n) :
    (p.snoc k).vertex ((m.castSucc).castSucc) = p.vertex m.castSucc ∧
      (p.snoc k).vertex ((m.castSucc).succ) = p.vertex m.succ := by
  constructor
  · exact Path.snoc_vertex_castSucc p k m.castSucc
  · rw [Fin.succ_castSucc, Path.snoc_vertex_castSucc]

lemma positivePath_snoc_iff {I : Type} {n : ℕ} {i k j : I}
    (M : Fin (n + 1) → Mat I) (p : Path I n i k)
    (hlast : 0 < M (Fin.last n) k j) :
    IsPositivePath M (p.snoc j) ↔
      IsPositivePath (fun m : Fin n => M m.castSucc) p := by
  constructor
  · intro h m
    have hm := h m.castSucc
    obtain ⟨h1, h2⟩ := snoc_edge_castSucc p j m
    simpa [IsPositivePath, h1, h2] using hm
  · intro h m
    cases m using Fin.lastCases with
    | last =>
        have hstart : (p.snoc j).vertex ((Fin.last n).castSucc) = k := by
          rw [Path.snoc_vertex_castSucc]
          exact p.finish
        have hend : (p.snoc j).vertex ((Fin.last n).succ) = j := by
          rw [Fin.succ_last, Path.snoc_vertex_last]
        rw [hstart, hend]
        exact hlast
    | cast m =>
        have hm := h m
        obtain ⟨h1, h2⟩ := snoc_edge_castSucc p j m
        simpa [IsPositivePath, h1, h2] using hm

lemma positivePath_prePath {I : Type} {n : ℕ} {i j : I}
    (M : Fin (n + 1) → Mat I) (p : Path I (n + 1) i j)
    (h : IsPositivePath M p) :
    IsPositivePath (fun m : Fin n => M m.castSucc) p.prePath ∧
      0 < M (Fin.last n) p.lastVertex j := by
  constructor
  · intro m
    have hm := h m.castSucc
    have hend : p.vertex ((m.castSucc).succ) = p.vertex (m.succ).castSucc := by
      rw [Fin.succ_castSucc]
    simpa [IsPositivePath, Path.prePath, hend] using hm
  · have hm := h (Fin.last n)
    have hstart : p.vertex ((Fin.last n).castSucc) = p.lastVertex := rfl
    have hend : p.vertex ((Fin.last n).succ) = j := by
      rw [Fin.succ_last]
      exact p.finish
    rw [hstart, hend] at hm
    exact hm

/-- Proposition 2.6(ii), in the stronger all-length form used as a lemma.
The source states it for `n ≥ 1`; the `n = 0` case is the empty product. -/
theorem orderedMatProd_pos_iff_exists_positivePath
    {I : Type} [Fintype I] [DecidableEq I] {n : ℕ}
    (M : Fin n → Mat I) (i j : I) :
    0 < orderedMatProd M i j ↔
      ∃ p : Path I n i j, IsPositivePath M p := by
  revert M i j
  induction n with
  | zero =>
      intro M i j
      constructor
      · intro h
        by_cases hij : i = j
        · subst j
          refine ⟨⟨fun _ => i, rfl, rfl⟩, ?_⟩
          intro m
          exact Fin.elim0 m
        · have hz : matId (I := I) i j = 0 := by simp [matId, hij]
          rw [orderedMatProd, hz] at h
          exact False.elim ((lt_irrefl (0 : ENNReal)) h)
      · rintro ⟨p, _hp⟩
        have hlast0 : Fin.last (0 : ℕ) = (0 : Fin 1) := rfl
        have hij : i = j := by
          calc
            i = p.vertex 0 := p.start.symm
            _ = p.vertex (Fin.last 0) := by rw [hlast0]
            _ = j := p.finish
        subst j
        simp [orderedMatProd, matId]
  | succ n ih =>
      intro M i j
      change 0 < matMul (M (Fin.last n))
          (orderedMatProd (fun k : Fin n => M k.castSucc)) i j ↔ _
      rw [matMul, Finset.sum_pos_iff_of_nonneg (fun k _ => zero_le _)]
      constructor
      · rintro ⟨k, _, hk⟩
        rw [ENNReal.mul_pos_iff] at hk
        obtain ⟨hlast, hpre⟩ := hk
        obtain ⟨p, hp⟩ :=
          (ih (fun m : Fin n => M m.castSucc) i k).1 hpre
        exact ⟨p.snoc j, (positivePath_snoc_iff M p hlast).2 hp⟩
      · rintro ⟨q, hq⟩
        obtain ⟨hpre, hlast⟩ := positivePath_prePath M q hq
        have hprod : 0 < orderedMatProd
            (fun m : Fin n => M m.castSucc) i q.lastVertex :=
          (ih (fun m : Fin n => M m.castSucc) i q.lastVertex).2
            ⟨q.prePath, hpre⟩
        refine ⟨q.lastVertex, Finset.mem_univ _, ?_⟩
        exact ENNReal.mul_pos (ne_of_gt hlast) (ne_of_gt hprod)

/-- Proposition 2.6(i), in the stronger all-length form used as a lemma. -/
theorem orderedMatProd_eq_zero_iff_forall_pathHasZero
    {I : Type} [Fintype I] [DecidableEq I] {n : ℕ}
    (M : Fin n → Mat I) (i j : I) :
    orderedMatProd M i j = 0 ↔
      ∀ p : Path I n i j, PathHasZero M p := by
  have hnot : orderedMatProd M i j = 0 ↔
      ¬ 0 < orderedMatProd M i j := by
    constructor
    · intro h
      rw [h]
      exact not_lt.mpr le_rfl
    · intro h
      exact le_antisymm (not_lt.mp h) (zero_le _)
  rw [hnot, orderedMatProd_pos_iff_exists_positivePath]
  constructor
  · intro h p
    by_contra hpz
    apply h
    refine ⟨p, ?_⟩
    intro m
    exact pos_iff_ne_zero.mpr (by
      intro hm
      exact hpz ⟨m, hm⟩)
  · rintro h ⟨p, hp⟩
    obtain ⟨m, hm⟩ := h p
    have hpos := hp m
    rw [hm] at hpos
    exact (lt_irrefl (0 : ENNReal)) hpos

/-- Proposition 2.6(ii) with the source's explicit nonempty-length hypothesis. -/
theorem orderedMatProd_pos_iff_exists_positivePath_of_pos
    {I : Type} [Fintype I] [DecidableEq I] {n : ℕ} (_hn : 0 < n)
    (M : Fin n → Mat I) (i j : I) :
    0 < orderedMatProd M i j ↔
      ∃ p : Path I n i j, IsPositivePath M p :=
  orderedMatProd_pos_iff_exists_positivePath M i j

/-- Proposition 2.6(i) with the source's explicit nonempty-length hypothesis. -/
theorem orderedMatProd_eq_zero_iff_forall_pathHasZero_of_pos
    {I : Type} [Fintype I] [DecidableEq I] {n : ℕ} (_hn : 0 < n)
    (M : Fin n → Mat I) (i j : I) :
    orderedMatProd M i j = 0 ↔
      ∀ p : Path I n i j, PathHasZero M p :=
  orderedMatProd_eq_zero_iff_forall_pathHasZero M i j

end

end OET.Chapter02
```

```lean filename=OET/Chapter02/Bounds.lean
import OET.Chapter02.Matrix

/-!
# Chapter 2: Lipschitz and co-Lipschitz matrix certificates

The predicates below follow the source convention: `L i j` (respectively
`K i j`) is the coefficient from input component `i` to output component `j`.
All inequalities involving `L` are upper bounds and all inequalities involving
`K` are lower bounds.
-/

namespace OET.Chapter02

open formal_oet.vol_01.ch_01_foundations

noncomputable section

variable {X : Type} {I : Type} [Fintype I] [DecidableEq I] {bot : X}

/-- A Lip matrix certificate on a restricted set `U ⊆ dom φ`. -/
def IsLipOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (L : Mat I) : Prop :=
  U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      d j (φ.func x) (φ.func y) ≤ ∑ i, L i j * d i x y

/-- A full-domain Lip certificate. -/
def IsLip (d : I → X → X → ENNReal) (φ : Operator X bot) (L : Mat I) : Prop :=
  IsLipOn d φ (dom φ) L

/-- The family of all restricted Lip certificates of `φ` on `U`. -/
def lipCertsOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (Mat I) :=
  {L | IsLipOn d φ U L}

/-- The family of all full-domain Lip certificates of `φ`. -/
def lipCerts (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  {L | IsLip d φ L}

/-- A restricted co-Lip certificate.  The nonemptiness condition is part of the
predicate, as in the source definition of `𝓚(φ)|_U`. -/
def IsCoLipOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X)
    (K : Mat I) : Prop :=
  U.Nonempty ∧ U ⊆ dom φ ∧
    ∀ x ∈ U, ∀ y ∈ U, ∀ j : I,
      (∑ i, K i j * d i x y) ≤ d j (φ.func x) (φ.func y)

/-- A full-domain co-Lip certificate. -/
def IsCoLip (d : I → X → X → ENNReal) (φ : Operator X bot) (K : Mat I) : Prop :=
  IsCoLipOn d φ (dom φ) K

/-- The family of all restricted co-Lip certificates of `φ` on `U`. -/
def coLipCertsOn (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) :
    Set (Mat I) :=
  {K | IsCoLipOn d φ U K}

/-- The family of all full-domain co-Lip certificates of `φ`. -/
def coLipCerts (d : I → X → X → ENNReal) (φ : Operator X bot) : Set (Mat I) :=
  {K | IsCoLip d φ K}

/-- In the single-component case the Lip sum has one summand. -/
theorem lip_single_component_scalar [Unique I]
    (d : I → X → X → ENNReal) (φ : Operator X bot) (U : Set X) (L : Mat I)
    (i : I) (hL : IsLipOn d φ U L) :
    ∀ x ∈ U, ∀ y ∈ U,
      d i (φ.func x) (φ.func y) ≤ L i i * d i x y := by
  intro x hx y hy
  have hsum : (∑ k : I, L k i * d k x y) = L i i * d i x y := by
    apply Finset.sum_eq_single (s := Finset.univ) (a := i)
      (f := fun k : I => L k i * d k x y)
    · intro k _ hki
      exact False.elim (hki (Subsingleton.elim k i))
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  have h := hL.2 x hx y hy i
  rw [hsum] at h
  exact h

/-- Restricted Lip certificate families are antitone in the restricted set. -/
theorem lipCertsOn_antitone
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U V : Set X}
    (hUV : U ⊆ V) (_hV : V ⊆ dom φ) :
    lipCertsOn d φ V ⊆ lipCertsOn d φ U := by
  intro L hL
  exact ⟨fun x hx => hL.1 (hUV hx),
    fun x hx y hy j => hL.2 x (hUV hx) y (hUV hy) j⟩

/-- A full-domain Lip certificate restricts to every subset of the domain. -/
theorem lipCerts_subset_lipCertsOn
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom φ) :
    lipCerts d φ ⊆ lipCertsOn d φ U := by
  intro L hL
  exact ⟨fun x hx => hL.1 (hU hx),
    fun x hx y hy j => hL.2 x (hU hx) y (hU hy) j⟩

/-- Restricted co-Lip certificate families are antitone, with the source's
nonemptiness hypotheses made explicit. -/
theorem coLipCertsOn_antitone
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U V : Set X}
    (hUne : U.Nonempty) (hUV : U ⊆ V) (_hV : V ⊆ dom φ) (_hVne : V.Nonempty) :
    coLipCertsOn d φ V ⊆ coLipCertsOn d φ U := by
  intro K hK
  exact ⟨hUne, fun x hx => hK.2.1 (hUV hx),
    fun x hx y hy j => hK.2.2 x (hUV hx) y (hUV hy) j⟩

/-- A full-domain co-Lip certificate restricts to every nonempty subset of the
domain. -/
theorem coLipCerts_subset_coLipCertsOn
    (d : I → X → X → ENNReal) (φ : Operator X bot) {U : Set X}
    (hUne : U.Nonempty) (hU : U ⊆ dom φ) :
    coLipCerts d φ ⊆ coLipCertsOn d φ U := by
  intro K hK
  exact ⟨hUne, hU,
    fun x hx y hy j => hK.2.2 x (hU hx) y (hU hy) j⟩

/-- A zero output distance together with a positive input distance forces the
corresponding co-Lip coefficient to vanish. -/
theorem coLip_entry_eq_zero_of_output_zero_input_pos
    (d : I → X → X → ENNReal) (φ : Operator X bot) (K : Mat I)
    (hK : IsCoLip d φ K) {i j : I} {x y : X}
    (hx : x ∈ dom φ) (hy : y ∈ dom φ)
    (hout : d j (φ.func x) (φ.func y) = 0)
    (hin : 0 < d i x y) :
    K i j = 0 := by
  have hterm : K i j * d i x y ≤ ∑ k, K k j * d k x y :=
    Finset.single_le_sum (f := fun k : I => K k j * d k x y)
      (fun k _ => zero_le _) (Finset.mem_univ i)
  have hle : K i j * d i x y ≤ 0 := by
    calc
      K i j * d i x y ≤ ∑ k, K k j * d k x y := hterm
      _ ≤ d j (φ.func x) (φ.func y) := hK.2.2 x hx y hy j
      _ = 0 := hout
  have hzero : K i j * d i x y = 0 := le_antisymm hle (zero_le _)
  by_contra hKij
  have hpos : 0 < K i j * d i x y :=
    ENNReal.mul_pos hKij (ne_of_gt hin)
  exact (ne_of_gt hpos) hzero

/-- The sum produced by the identity matrix collapses to the corresponding
component distance. -/
lemma matId_sum_dist (d : I → X → X → ENNReal) (x y : X) (j : I) :
    (∑ i : I, matId i j * d i x y) = d j x y := by
  simp [matId, Finset.sum_ite_eq']

/-- The identity matrix is a Lip certificate for the identity operator on every
subset of the identity operator's domain. -/
theorem lip_identity
    (d : I → X → X → ENNReal) (U : Set X)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    IsLipOn d (1 : Operator X bot) U matId := by
  refine ⟨hU, ?_⟩
  intro x hx y hy j
  rw [matId_sum_dist]
  rfl

/-- The identity matrix is a co-Lip certificate for the identity operator on
every nonempty subset of its domain. -/
theorem coLip_identity
    (d : I → X → X → ENNReal) (U : Set X) (hUne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    IsCoLipOn d (1 : Operator X bot) U matId := by
  refine ⟨hUne, hU, ?_⟩
  intro x hx y hy j
  rw [matId_sum_dist]
  rfl

theorem matId_mem_lipCertsOn_identity
    (d : I → X → X → ENNReal) (U : Set X)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    matId ∈ lipCertsOn d (1 : Operator X bot) U :=
  lip_identity d U hU

theorem matId_mem_coLipCertsOn_identity
    (d : I → X → X → ENNReal) (U : Set X) (hUne : U.Nonempty)
    (hU : U ⊆ dom (1 : Operator X bot)) :
    matId ∈ coLipCertsOn d (1 : Operator X bot) U :=
  coLip_identity d U hUne hU


/-- The domain of a composite is contained in the domain of its inner
operator. -/
lemma dom_mul_subset_right {X : Type} {bot : X} (φ ψ : Operator X bot) :
    dom (φ * ψ) ⊆ dom ψ := by
  intro x hx
  dsimp [dom] at hx ⊢
  change φ.func (ψ.func x) ≠ bot at hx
  intro hψ
  rw [hψ, φ.preserves_bot] at hx
  exact hx rfl

/-- The actual intermediate image of a composite is contained in the outer
operator's domain. -/
lemma image_subset_dom_of_subset_dom_comp
    {X : Type} {bot : X} (φ₁ φ₂ : Operator X bot) {U : Set X}
    (hU : U ⊆ dom (φ₂ * φ₁)) :
    φ₁.func '' U ⊆ dom φ₂ := by
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hU hx
  dsimp [dom] at hx' ⊢
  exact hx'

/-- Reassociate the double sum appearing in a two-step matrix bound.  This is
the ENNReal form of distributing a finite sum and exchanging summations. -/
lemma sum_comp_coeff {I : Type} [Fintype I]
    (A B : Mat I) (f : I → ENNReal) (j : I) :
    (∑ k, A k j * (∑ i, B i k * f i)) =
      ∑ i, (∑ k, A k j * B i k) * f i := by
  calc
    (∑ k, A k j * (∑ i, B i k * f i))
        = ∑ k, ∑ i, A k j * (B i k * f i) := by
            apply Finset.sum_congr rfl
            intro k _
            rw [Finset.mul_sum]
    _ = ∑ i, ∑ k, A k j * (B i k * f i) := Finset.sum_comm
    _ = ∑ i, ∑ k, (A k j * B i k) * f i := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro k _
            rw [mul_assoc]
    _ = ∑ i, (∑ k, A k j * B i k) * f i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]

/-- Proposition 2.2: the two-step Lip composition law with the exact
intermediate image `φ₁ '' U₁`, and with the matrix product in the order
`L₂ · L₁`. -/
theorem lip_comp_two
    (d : I → X → X → ENNReal) (φ₁ φ₂ : Operator X bot)
    (U₁ U₂ : Set X) (L₁ L₂ : Mat I)
    (hU₂ : U₂ = φ₁.func '' U₁)
    (hcomp : U₁ ⊆ dom (φ₂ * φ₁))
    (h₁ : IsLipOn d φ₁ U₁ L₁)
    (h₂ : IsLipOn d φ₂ U₂ L₂) :
    IsLipOn d (φ₂ * φ₁) U₁ (matMul L₂ L₁) := by
  refine ⟨hcomp, ?_⟩
  intro x hx y hy j
  have hx₂ : φ₁.func x ∈ U₂ := by
    rw [hU₂]
    exact ⟨x, hx, rfl⟩
  have hy₂ : φ₁.func y ∈ U₂ := by
    rw [hU₂]
    exact ⟨y, hy, rfl⟩
  have h₂ineq :
      d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) ≤
        ∑ k, L₂ k j * d k (φ₁.func x) (φ₁.func y) :=
    h₂.2 (φ₁.func x) hx₂ (φ₁.func y) hy₂ j
  have h₁ineq :
      ∀ k : I, d k (φ₁.func x) (φ₁.func y) ≤
        ∑ i, L₁ i k * d i x y :=
    fun k => h₁.2 x hx y hy k
  calc
    d j ((φ₂ * φ₁).func x) ((φ₂ * φ₁).func y)
        = d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) := rfl
    _ ≤ ∑ k, L₂ k j * d k (φ₁.func x) (φ₁.func y) := h₂ineq
    _ ≤ ∑ k, L₂ k j * (∑ i, L₁ i k * d i x y) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_right (h₁ineq k) (L₂ k j)
    _ = ∑ i, matMul L₂ L₁ i j * d i x y := by
          rw [sum_comp_coeff]
          rfl

/-- Proposition 2.4: the two-step co-Lip composition law with the exact
intermediate image `φ₁ '' U₁` and nonemptiness inherited from `U₁`. -/
theorem coLip_comp_two
    (d : I → X → X → ENNReal) (φ₁ φ₂ : Operator X bot)
    (U₁ U₂ : Set X) (K₁ K₂ : Mat I)
    (hU₂ : U₂ = φ₁.func '' U₁)
    (hcomp : U₁ ⊆ dom (φ₂ * φ₁))
    (h₁ : IsCoLipOn d φ₁ U₁ K₁)
    (h₂ : IsCoLipOn d φ₂ U₂ K₂) :
    IsCoLipOn d (φ₂ * φ₁) U₁ (matMul K₂ K₁) := by
  refine ⟨h₁.1, hcomp, ?_⟩
  intro x hx y hy j
  have hx₂ : φ₁.func x ∈ U₂ := by
    rw [hU₂]
    exact ⟨x, hx, rfl⟩
  have hy₂ : φ₁.func y ∈ U₂ := by
    rw [hU₂]
    exact ⟨y, hy, rfl⟩
  have h₂ineq :
      (∑ k, K₂ k j * d k (φ₁.func x) (φ₁.func y)) ≤
        d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) :=
    h₂.2.2 (φ₁.func x) hx₂ (φ₁.func y) hy₂ j
  have h₁ineq :
      ∀ k : I, (∑ i, K₁ i k * d i x y) ≤
        d k (φ₁.func x) (φ₁.func y) :=
    fun k => h₁.2.2 x hx y hy k
  calc
    (∑ i, matMul K₂ K₁ i j * d i x y)
        = ∑ k, K₂ k j * (∑ i, K₁ i k * d i x y) := by
            rw [sum_comp_coeff]
            rfl
    _ ≤ ∑ k, K₂ k j * d k (φ₁.func x) (φ₁.func y) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_right (h₁ineq k) (K₂ k j)
    _ ≤ d j (φ₂.func (φ₁.func x)) (φ₂.func (φ₁.func y)) := h₂ineq
    _ = d j ((φ₂ * φ₁).func x) ((φ₂ * φ₁).func y) := rfl

end

end OET.Chapter02
```

```lean filename=OET/Chapter02/Chains.lean
import OET.Chapter02.Bounds

/-!
# Chapter 2: finite operator chains and intermediate image domains

For a finite family `φ : Fin n → Operator X bot`, `composeChain φ` is the
textbook chain `φ (n-1) ∘ ... ∘ φ 0`.  The structure `IntermediateImages`
records the actual intermediate image sets
`U₀, φ₀(U₀), φ₁(φ₀(U₀)), ...` of the chain.
-/

namespace OET.Chapter02

open formal_oet.vol_01.ch_01_foundations

noncomputable section

variable {X : Type} {I : Type} [Fintype I] [DecidableEq I] {bot : X}

/-- Ordered composition of a finite family of operators.  Index `0` is the
first operator applied; therefore index `n-1` is the outermost operator. -/
def composeChain {X : Type} {bot : X} :
    {n : ℕ} → (Fin n → Operator X bot) → Operator X bot
  | 0, _ => 1
  | n + 1, φ => φ (Fin.last n) * composeChain (fun k : Fin n => φ k.castSucc)

@[simp]
theorem composeChain_zero {X : Type} {bot : X}
    (φ : Fin 0 → Operator X bot) :
    composeChain φ = 1 := rfl

@[simp]
theorem composeChain_succ {X : Type} {bot : X} {n : ℕ}
    (φ : Fin (n + 1) → Operator X bot) :
    composeChain φ =
      φ (Fin.last n) * composeChain (fun k : Fin n => φ k.castSucc) := rfl

/-- Actual intermediate image domains of a finite chain. -/
structure IntermediateImages {X : Type} {bot : X} (U₀ : Set X)
    {n : ℕ} (φ : Fin n → Operator X bot) where
  stage : Fin (n + 1) → Set X
  stage_zero : stage 0 = U₀
  stage_succ : ∀ m : Fin n, stage m.succ = (φ m).func '' stage m.castSucc

namespace IntermediateImages

/-- Forget the last operator and last stage of an intermediate-image family. -/
def take {X : Type} {bot : X} {U₀ : Set X} {n : ℕ}
    {φ : Fin (n + 1) → Operator X bot}
    (U : IntermediateImages U₀ φ) :
    IntermediateImages U₀ (fun m : Fin n => φ m.castSucc) where
  stage k := U.stage k.castSucc
  stage_zero := by
    simpa using U.stage_zero
  stage_succ m := by
    have h := U.stage_succ m.castSucc
    rw [Fin.succ_castSucc] at h
    exact h

/-- The last recorded stage is exactly the image of the full composite. -/
theorem stage_last_eq_comp_image
    {X : Type} {bot : X} {U₀ : Set X} :
    ∀ {n : ℕ} {φ : Fin n → Operator X bot}
      (U : IntermediateImages U₀ φ),
      (composeChain φ).func '' U₀ = U.stage (Fin.last n) := by
  intro n
  induction n with
  | zero =>
      intro φ U
      have hcomp : composeChain φ = (1 : Operator X bot) := rfl
      rw [hcomp]
      have himg : (1 : Operator X bot).func '' U₀ = U₀ := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨x, hx, rfl⟩
      rw [himg]
      simpa using U.stage_zero.symm
  | succ n ih =>
      intro φ U
      let preφ : Fin n → Operator X bot := fun m => φ m.castSucc
      have himage_comp :
          (φ (Fin.last n) * composeChain preφ).func '' U₀ =
            Set.image (φ (Fin.last n)).func
              (Set.image (composeChain preφ).func U₀) := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨(composeChain preφ).func x, ⟨x, hx, rfl⟩, rfl⟩
        · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, rfl⟩
      rw [composeChain, himage_comp]
      have hpre := ih (φ := preφ) (U := U.take)
      rw [hpre]
      have hstage : U.take.stage (Fin.last n) =
          U.stage (Fin.last n).castSucc := rfl
      rw [hstage, ← U.stage_succ (Fin.last n), Fin.succ_last]

end IntermediateImages



/-- Corollary 2.5 at the zero-step boundary (for Lip): the empty ordered product
is the identity matrix, and the zero-step chain is the identity operator. -/
theorem lip_chain_zero_step
    (d : I → X → X → ENNReal)
    (φ : Fin 0 → Operator X bot) (L : Fin 0 → Mat I) (U₀ : Set X)
    (hU : U₀ ⊆ dom (composeChain φ)) :
    IsLipOn d (composeChain φ) U₀ (orderedMatProd L) := by
  simpa [composeChain, orderedMatProd] using lip_identity d U₀ hU

/-- Corollary 2.5 at the zero-step boundary (for co-Lip): the empty ordered
product is the identity matrix, and the zero-step chain is the identity
operator. -/
theorem coLip_chain_zero_step
    (d : I → X → X → ENNReal)
    (φ : Fin 0 → Operator X bot) (L : Fin 0 → Mat I) (U₀ : Set X)
    (hUne : U₀.Nonempty) (hU : U₀ ⊆ dom (composeChain φ)) :
    IsCoLipOn d (composeChain φ) U₀ (orderedMatProd L) := by
  simpa [composeChain, orderedMatProd] using coLip_identity d U₀ hUne hU

/-- Corollary 2.5(i), chain form.  The step certificates are given on the
actual intermediate domains recorded by `U`, and the resulting certificate is
the ordered product of the step matrices. -/
theorem lip_chain_of_step_certs_aux
    (d : I → X → X → ENNReal) :
    ∀ {n : ℕ} (φ : Fin n → Operator X bot) (L : Fin n → Mat I)
      (U₀ : Set X) (U : IntermediateImages U₀ φ),
      U₀ ⊆ dom (composeChain φ) →
      (∀ m : Fin n,
        IsLipOn d (φ m) (U.stage m.castSucc) (L m)) →
      IsLipOn d (composeChain φ) U₀ (orderedMatProd L) := by
  intro n
  induction n with
  | zero =>
      intro φ L U₀ U hU _hcert
      simpa [composeChain, orderedMatProd] using lip_identity d U₀ hU
  | succ n ih =>
      intro φ L U₀ U hU hcert
      let preφ : Fin n → Operator X bot := fun m => φ m.castSucc
      let preL : Fin n → Mat I := fun m => L m.castSucc
      have hU' : U₀ ⊆ dom (φ (Fin.last n) * composeChain preφ) := by
        simpa [composeChain, preφ] using hU
      have hU_pre : U₀ ⊆ dom (composeChain preφ) :=
        fun x hx => dom_mul_subset_right (φ (Fin.last n))
          (composeChain preφ) (hU' hx)
      have hcert_pre : ∀ m : Fin n,
          IsLipOn d (preφ m) (U.take.stage m.castSucc) (preL m) := by
        intro m
        have h := hcert m.castSucc
        simpa [preφ, preL, IntermediateImages.take] using h
      have hIH := ih (φ := preφ) (L := preL) (U₀ := U₀)
        (U := U.take) hU_pre hcert_pre
      have hstage := IntermediateImages.stage_last_eq_comp_image
        (U := U.take)
      have hlast : IsLipOn d (φ (Fin.last n))
          ((composeChain preφ).func '' U₀) (L (Fin.last n)) := by
        rw [hstage]
        have h := hcert (Fin.last n)
        simpa [IntermediateImages.take] using h
      have hfull := lip_comp_two d (composeChain preφ) (φ (Fin.last n))
        U₀ ((composeChain preφ).func '' U₀)
        (orderedMatProd preL) (L (Fin.last n)) rfl hU' hIH hlast
      simpa [composeChain, orderedMatProd, preφ, preL] using hfull

/-- Corollary 2.5(ii), chain form.  The step co-Lip certificates are given on
the actual intermediate domains recorded by `U`; their nonemptiness supplies
the nonemptiness required at each stage. -/
theorem coLip_chain_of_step_certs_aux
    (d : I → X → X → ENNReal) :
    ∀ {n : ℕ} (φ : Fin n → Operator X bot) (L : Fin n → Mat I)
      (U₀ : Set X) (U : IntermediateImages U₀ φ),
      U₀.Nonempty →
      U₀ ⊆ dom (composeChain φ) →
      (∀ m : Fin n,
        IsCoLipOn d (φ m) (U.stage m.castSucc) (L m)) →
      IsCoLipOn d (composeChain φ) U₀ (orderedMatProd L) := by
  intro n
  induction n with
  | zero =>
      intro φ L U₀ U hne hU _hcert
      simpa [composeChain, orderedMatProd] using coLip_identity d U₀ hne hU
  | succ n ih =>
      intro φ L U₀ U hne hU hcert
      let preφ : Fin n → Operator X bot := fun m => φ m.castSucc
      let preL : Fin n → Mat I := fun m => L m.castSucc
      have hU' : U₀ ⊆ dom (φ (Fin.last n) * composeChain preφ) := by
        simpa [composeChain, preφ] using hU
      have hU_pre : U₀ ⊆ dom (composeChain preφ) :=
        fun x hx => dom_mul_subset_right (φ (Fin.last n))
          (composeChain preφ) (hU' hx)
      have hcert_pre : ∀ m : Fin n,
          IsCoLipOn d (preφ m) (U.take.stage m.castSucc) (preL m) := by
        intro m
        have h := hcert m.castSucc
        simpa [preφ, preL, IntermediateImages.take] using h
      have hIH := ih (φ := preφ) (L := preL) (U₀ := U₀)
        (U := U.take) hne hU_pre hcert_pre
      have hstage := IntermediateImages.stage_last_eq_comp_image
        (U := U.take)
      have hlast : IsCoLipOn d (φ (Fin.last n))
          ((composeChain preφ).func '' U₀) (L (Fin.last n)) := by
        rw [hstage]
        have h := hcert (Fin.last n)
        simpa [IntermediateImages.take] using h
      have hfull := coLip_comp_two d (composeChain preφ) (φ (Fin.last n))
        U₀ ((composeChain preφ).func '' U₀)
        (orderedMatProd preL) (L (Fin.last n)) rfl hU' hIH hlast
      simpa [composeChain, orderedMatProd, preφ, preL] using hfull

/-- Corollary 2.5(i) with the source's positive-length hypothesis. -/
theorem lip_chain_of_step_certs
    (d : I → X → X → ENNReal) {n : ℕ} (_hn : 0 < n)
    (φ : Fin n → Operator X bot) (L : Fin n → Mat I)
    (U₀ : Set X) (U : IntermediateImages U₀ φ)
    (hU : U₀ ⊆ dom (composeChain φ))
    (hcert : ∀ m : Fin n,
      IsLipOn d (φ m) (U.stage m.castSucc) (L m)) :
    IsLipOn d (composeChain φ) U₀ (orderedMatProd L) :=
  lip_chain_of_step_certs_aux d φ L U₀ U hU hcert

/-- Corollary 2.5(ii) with the source's positive-length hypothesis.  The
nonemptiness of `U₀` is derived from the first step co-Lip certificate. -/
theorem coLip_chain_of_step_certs
    (d : I → X → X → ENNReal) {n : ℕ} (_hn : 0 < n)
    (φ : Fin n → Operator X bot) (L : Fin n → Mat I)
    (U₀ : Set X) (U : IntermediateImages U₀ φ)
    (hU : U₀ ⊆ dom (composeChain φ))
    (hcert : ∀ m : Fin n,
      IsCoLipOn d (φ m) (U.stage m.castSucc) (L m)) :
    IsCoLipOn d (composeChain φ) U₀ (orderedMatProd L) := by
  have hn' : 0 < n := _hn
  have hne : U₀.Nonempty := by
    have h := (hcert ⟨0, hn'⟩).1
    have h0 : U.stage (0 : Fin (n + 1)) = U₀ := U.stage_zero
    simpa [h0] using h
  exact coLip_chain_of_step_certs_aux d φ L U₀ U hne hU hcert

end

end OET.Chapter02
```

```lean filename=Main.lean
import OET.Chapter02.Matrix
import OET.Chapter02.Bounds
import OET.Chapter02.Chains

/-!
# LCH02 deliverable entry point

This module imports all Chapter 2 formalization modules:
* `OET.Chapter02.Matrix`: matrix convention, ordered products and path criteria.
* `OET.Chapter02.Bounds`: Lip/co-Lip predicates and their basic laws.
* `OET.Chapter02.Chains`: finite chains, intermediate images and chain bounds.
-/
```

```lean filename=lakefile.lean
-- LCH02 candidate project.
import Lake
open Lake DSL

package benchmarkCandidate
require mathlib from "/Users/glen/lab/benchmark/preparation-v0.3.0-tcodex-20261103/env/mathlib"

@[default_target]
lean_lib BenchmarkCandidate where
  roots := #[`Main,
    `«OET».«Chapter02».«Matrix», `«OET».«Chapter02».«Bounds», `«OET».«Chapter02».«Chains»,
    `«formal_oet».«vol_01».«ch_01_foundations».«gauge_space»,
    `«formal_oet».«vol_01».«ch_01_foundations».«operator_space»]
```

```json filename=alignment.json
{
  "case_id": "LCH02",
  "version": "0.1.0",
  "items": [
    {
      "id": "CH02-D01",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.IsLipOn"
        },
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.IsLip"
        },
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.lipCertsOn"
        },
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.lipCerts"
        }
      ],
      "representation": "对象：有限指标类型 I、带吸收元 bot 的点空间 X、规范族 d : I → X → X → ENNReal、算子 φ : Operator X bot、矩阵 L。受限谓词 IsLipOn d φ U L 量词为 x,y∈U 与 j∈I，结论为 d j (φ x) (φ y) ≤ ∑ i, L i j * d i x y，并含 U⊆dom φ；IsLip 取 U=dom φ。lipCertsOn/lipCerts 是相应合法矩阵的证书族。矩阵条目 L i j 的 i 是输入分量、j 是输出分量。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D02",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.IsCoLipOn"
        },
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.IsCoLip"
        },
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.coLipCertsOn"
        },
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.coLipCerts"
        }
      ],
      "representation": "对象同上，K 为 co-Lip 矩阵。IsCoLipOn d φ U K 的首个字段是 U.Nonempty，其次为 U⊆dom φ，结论为 ∑ i, K i j * d i x y ≤ d j (φ x) (φ y)（x,y∈U、j∈I）；IsCoLip 取 U=dom φ。coLipCertsOn/coLipCerts 仅收集满足含非空条件的三元证书。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D03",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.Mat"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.matMul"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.matMul_apply"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.matMul_assoc"
        }
      ],
      "representation": "Mat I := I → I → ENNReal；按原文行列约定，M i j 位于输出分量 j 的行、输入分量 i 的列。matMul M₂ M₁ i j = ∑ k, M₂ k j * M₁ i k，即两步复合 φ₂∘φ₁ 的矩阵乘积为 M₂·M₁；matMul_apply 给出定义等式，matMul_assoc 证明该有限 ENNReal 矩阵乘法结合。",
      "dependencies": []
    },
    {
      "id": "CH02-D04",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.matId"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.matId_apply"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.matMul_matId"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.matId_matMul"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.orderedMatProd"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.orderedMatProd_zero"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.orderedMatProd_succ"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.orderedMatProd_one"
        }
      ],
      "representation": "matId i j = if i=j then 1 else 0，并用 matMul_matId、matId_matMul 证明它是双侧单位矩阵。orderedMatProd 对族 M : Fin n → Mat I 递归定义：空族为零步乘积 matId；n+1 步时把最后一个矩阵放在外侧，即 M_last·(前缀乘积)。orderedMatProd_one 说明单步有序乘积等于原矩阵。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-D05",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.composeChain"
        },
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.composeChain_zero"
        },
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.composeChain_succ"
        },
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.IntermediateImages"
        },
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.IntermediateImages.take"
        },
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.IntermediateImages.stage_last_eq_comp_image"
        }
      ],
      "representation": "composeChain φ 对 φ : Fin n → Operator X bot 的实现按原文 c_k=φ_k∘…∘φ_1：索引 0 先作用，递归时最后一项在外侧；n=0 时为单位算子。IntermediateImages U₀ φ 用 stage : Fin(n+1)→Set X、stage_zero 与 stage_succ: stage(m+1)=φ_m(stage m) 记录实际中间像域。stage_last_eq_comp_image 证明整条链的复合像恰为最后 stage，完成链表示与中间域对应。",
      "dependencies": []
    },
    {
      "id": "CH02-D06",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.Path"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.Path.snoc"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.Path.prePath"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.Path.lastVertex"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.IsPositivePath"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.PathHasZero"
        }
      ],
      "representation": "Path I n i j 由 Fin(n+1) 个顶点及起点/终点等式构成；n 条边的第 m 条从 vertex(m.castSucc) 到 vertex(m.succ)。IsPositivePath M p 量词为所有 m:Fin n，结论为对应矩阵条目 0<M m ...；PathHasZero M p 表示存在某条边对应条目等于 0。n=1 时路径只有一条边。",
      "dependencies": [
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P01",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.lip_single_component_scalar"
        }
      ],
      "representation": "用 [Unique I] 表示 |I|=1 且 I={i} 的单分量情形。给定受限 Lip 证书 IsLipOn d φ U L，结论对 x,y∈U 有 d i (φ x) (φ y) ≤ L i i * d i x y；证明中 ∑ k, L k i * d k x y 退化为唯一项 L i i*d i x y。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P02",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.lipCertsOn_antitone"
        }
      ],
      "representation": "前提 U⊆V、V⊆dom φ；结论为集合包含 lipCertsOn d φ V ⊆ lipCertsOn d φ U。成员 L 在 V 上的 Lip 不等式逐点限制到 U，量词和结论强度不变。",
      "dependencies": [
        "CH02-D01"
      ]
    },
    {
      "id": "CH02-P04",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.lip_comp_two"
        }
      ],
      "representation": "取 φ₁ φ₂、起始域 U₁，并以等式 U₂=φ₁(U₁) 表示精确中间像域；前提 U₁⊆dom(φ₂∘φ₁)、L₁∈Lip(φ₁)|U₁、L₂∈Lip(φ₂)|U₂。结论为 IsLipOn d (φ₂∘φ₁) U₁ (matMul L₂ L₁)，即外层 L₂ 在左、内层 L₁ 在右，完全沿用原文乘积次序。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P05",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.coLipCertsOn_antitone"
        }
      ],
      "representation": "前提 ∅≠U⊆V、V⊆dom φ、V≠∅（并在证书族成员中仍保留 V⊆dom φ）；结论为 coLipCertsOn d φ V ⊆ coLipCertsOn d φ U。co-Lip 下界不等式限制到 U，非空性由前提 U.Nonempty 提供。",
      "dependencies": [
        "CH02-D02"
      ]
    },
    {
      "id": "CH02-P07",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.coLip_entry_eq_zero_of_output_zero_input_pos"
        }
      ],
      "representation": "给定全域 co-Lip 证书 K∈K(φ)|dom(φ)、x,y∈dom φ、d j (φx)(φy)=0 且 0<d i x y。由 co-Lip 不等式和非负有限和，K i j*d i x y≤0，因 d i x y>0 得 K i j=0；条目方向保持 i→j。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P08",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.coLip_comp_two"
        },
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.dom_mul_subset_right"
        },
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.image_subset_dom_of_subset_dom_comp"
        }
      ],
      "representation": "取 φ₁ φ₂、U₂=φ₁(U₁) 的精确中间像域、U₁⊆dom(φ₂∘φ₁) 及 K₁∈K(φ₁)|U₁、K₂∈K(φ₂)|U₂。结论 IsCoLipOn d (φ₂∘φ₁) U₁ (matMul K₂ K₁)，其非空性来自 U₁.Nonempty，中间域非空来自 K₂ 的证书；辅助引理说明实际中间像包含于外层定义域。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03"
      ]
    },
    {
      "id": "CH02-P11",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.lip_identity"
        },
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.matId_mem_lipCertsOn_identity"
        },
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.lip_chain_zero_step"
        }
      ],
      "representation": "对任意 U⊆dom(id_X)，证明 IsLipOn d id_X U matId，从而 matId∈L(id_X)|U；等式 d j x y≤∑ i matId i j*d i x y 化为等式。lip_chain_zero_step 直接给出零步链 composeChain(Fin 0)=id_X 与空有序乘积 matId 的 Lip 证书。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05"
      ]
    },
    {
      "id": "CH02-P12",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.coLip_identity"
        },
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.matId_mem_coLipCertsOn_identity"
        },
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.coLip_chain_zero_step"
        }
      ],
      "representation": "对非空 U⊆dom(id_X)，证明 IsCoLipOn d id_X U matId，从而 matId∈K(id_X)|U；co-Lip 下界同样由 matId 求和恒等式化为等号。coLip_chain_zero_step 给出零步链与空乘积的单位 co-Lip 证书。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05"
      ]
    },
    {
      "id": "CH02-P14",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.orderedMatProd_pos_iff_exists_positivePath"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.orderedMatProd_pos_iff_exists_positivePath_of_pos"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.positivePath_snoc_iff"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.positivePath_prePath"
        }
      ],
      "representation": "对 M:Fin n→Mat I、端点 i,j，核心定理证明 0<orderedMatProd M i j ↔ ∃p:Path I n i j, IsPositivePath M p。路径边按 m=0,…,n-1 排列，矩阵乘积按 n-1,…,0 排列，故每条路径乘积与对应矩阵乘积项完全一致。_of_pos 版本显式加入 n≥1，包含 n=1 的空中间指标情形。",
      "dependencies": [
        "CH02-D03",
        "CH02-D04",
        "CH02-D06"
      ]
    },
    {
      "id": "CH02-P03",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.lipCerts_subset_lipCertsOn"
        }
      ],
      "representation": "前提 U⊆dom φ；结论 lipCerts d φ ⊆ lipCertsOn d φ U。全域 Lip 证书在 U⊆dom φ 上逐点限制，得到原证书族在受限域上的成员关系。",
      "dependencies": [
        "CH02-D01"
      ]
    },
    {
      "id": "CH02-P06",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Bounds.lean",
          "name": "OET.Chapter02.coLipCerts_subset_coLipCertsOn"
        }
      ],
      "representation": "前提 U≠∅ 且 U⊆dom φ；结论 coLipCerts d φ ⊆ coLipCertsOn d φ U。全域 co-Lip 证书限制到非空子集，非空条件显式保留。",
      "dependencies": [
        "CH02-D02"
      ]
    },
    {
      "id": "CH02-P09",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.lip_chain_of_step_certs_aux"
        },
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.lip_chain_of_step_certs"
        }
      ],
      "representation": "对正长度 n、φ:Fin n→Operator X bot、逐步矩阵 L:Fin n→Mat I 及实际中间域族 U:IntermediateImages U₀ φ，前提为 U₀⊆dom(composeChain φ) 与每个 m 的 IsLipOn d (φ m) (U.stage m) (L m)。结论为 IsLipOn d (composeChain φ) U₀ (orderedMatProd L)，即任意正长度链的 Lip 连乘界；归纳证明由两步复合律和中间像精确性完成。",
      "dependencies": [
        "CH02-D01",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05",
        "CH02-P04",
        "CH02-P11"
      ]
    },
    {
      "id": "CH02-P10",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.coLip_chain_of_step_certs_aux"
        },
        {
          "file": "OET/Chapter02/Chains.lean",
          "name": "OET.Chapter02.coLip_chain_of_step_certs"
        }
      ],
      "representation": "对正长度 n、逐步 co-Lip 证书 IsCoLipOn d (φ m) (U.stage m) (L m)，前提另含 U₀⊆dom(composeChain φ)。结论为 IsCoLipOn d (composeChain φ) U₀ (orderedMatProd L)；U₀ 非空性由第一张 co-Lip 证书自动推出，连乘次序与 Lip 链完全一致。",
      "dependencies": [
        "CH02-D02",
        "CH02-D03",
        "CH02-D04",
        "CH02-D05",
        "CH02-P08",
        "CH02-P12"
      ]
    },
    {
      "id": "CH02-P13",
      "status": "complete",
      "declarations": [
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.orderedMatProd_eq_zero_iff_forall_pathHasZero"
        },
        {
          "file": "OET/Chapter02/Matrix.lean",
          "name": "OET.Chapter02.orderedMatProd_eq_zero_iff_forall_pathHasZero_of_pos"
        }
      ],
      "representation": "核心定理证明 orderedMatProd M i j=0 ↔ ∀p:Path I n i j, PathHasZero M p，即矩阵乘积条目为零当且仅当每条指标路径至少含一个零因子；由 P14 的正值路径判据取非并利用 ENNReal 非负性得到。_of_pos 版本显式限制 n≥1，n=1 时退化为单矩阵条目判据。",
      "dependencies": [
        "CH02-D03",
        "CH02-D04",
        "CH02-D06",
        "CH02-P14"
      ]
    }
  ]
}
```