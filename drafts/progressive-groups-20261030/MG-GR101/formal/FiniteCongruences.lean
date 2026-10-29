import CongruenceObstruction

noncomputable section
open MathGauge.R101

namespace MathGauge.GR101
variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

def pairRecords (A B : Submodule R M) : Submodule R (M × M) where
  carrier := {r | r.1 - r.2 ∈ A ⊔ B}
  zero_mem' := by simp
  add_mem' := by
    intro r s hr hs
    change r.1 + s.1 - (r.2 + s.2) ∈ A ⊔ B
    convert (A ⊔ B).add_mem hr hs using 1 <;> abel
  smul_mem' := by
    intro a r hr
    simpa [smul_sub] using (A ⊔ B).smul_mem a hr

def pairNoise (A B : Submodule R M) : Submodule R (pairRecords A B) where
  carrier := {r | r.val.1 ∈ A ∧ r.val.2 ∈ B}
  zero_mem' := by simp
  add_mem' := fun h k => ⟨A.add_mem h.1 k.1, B.add_mem h.2 k.2⟩
  smul_mem' := fun a _ h => ⟨A.smul_mem a h.1, B.smul_mem a h.2⟩

def pairDiagonal (A B : Submodule R M) : M →ₗ[R] pairRecords A B where
  toFun x := ⟨(x, x), by simp [pairRecords]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pairMap (A B : Submodule R M) : M →ₗ[R] pairRecords A B ⧸ pairNoise A B :=
  (pairNoise A B).mkQ.comp (pairDiagonal A B)

theorem pairMap_kernel (A B : Submodule R M) : (pairMap A B).ker = A ⊓ B := by
  ext x
  change (Submodule.Quotient.mk (pairDiagonal A B x) : pairRecords A B ⧸ pairNoise A B) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

theorem pairMap_surjective (A B : Submodule R M) : Function.Surjective (pairMap A B) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H r =>
      obtain ⟨w, hw⟩ := partial_exists r.property
      refine ⟨w, ?_⟩
      apply (Submodule.Quotient.eq _).mpr
      exact hw

/-- S1: the actual quotient of compatible pairs, not the ambient product quotient. -/
def pairEquiv (A B : Submodule R M) :
    (M ⧸ (A ⊓ B)) ≃ₗ[R] (pairRecords A B ⧸ pairNoise A B) :=
  (Submodule.quotEquivOfEq _ _ (pairMap_kernel A B).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (pairMap_surjective A B))

theorem pairEquiv_on_diagonal (A B : Submodule R M) (x : M) :
    pairEquiv A B (Submodule.Quotient.mk x) = pairMap A B x := rfl

theorem pair_fiber {A B : Submodule R M} {x y w t : M}
    (hw : PartialGlue A B x y w) :
    PartialGlue A B x y t ↔ t - w ∈ A ⊓ B := by
  constructor
  · exact fun ht => partial_difference ht hw
  · intro h
    constructor
    · convert A.add_mem h.1 hw.1 using 1 <;> abel
    · convert B.add_mem h.2 hw.2 using 1 <;> abel

/-- S2 uses only the stated distributive identity for these three submodules. -/
theorem triple_glue {A B C : Submodule R M}
    (hEq : (A ⊔ C) ⊓ (B ⊔ C) = (A ⊓ B) ⊔ C)
    {x y z : M} (h : Compatible A B C x y z) : ∃ t, Glues A B C x y z t := by
  obtain ⟨w, hw⟩ := partial_exists h.1
  apply (obstruction_zero_iff hw).mp
  change w - z ∈ (A ⊓ B) ⊔ C
  rw [← hEq]
  exact obstruction_mem h hw

theorem triple_embedding_surjective {A B C : Submodule R M}
    (hEq : (A ⊔ C) ⊓ (B ⊔ C) = (A ⊓ B) ⊔ C) :
    Function.Surjective (residue_embedding A B C) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H r =>
      obtain ⟨w, hw⟩ := triple_glue hEq r.property
      exact ⟨Submodule.Quotient.mk w, ((same_record_iff r w).mpr hw).symm⟩

def tripleEquiv {A B C : Submodule R M}
    (hEq : (A ⊔ C) ⊓ (B ⊔ C) = (A ⊓ B) ⊔ C) :
    (M ⧸ ((A ⊓ B) ⊓ C)) ≃ₗ[R] (records A B C ⧸ noise A B C) :=
  LinearEquiv.ofBijective (residue_embedding A B C)
    ⟨residue_embedding_injective A B C, triple_embedding_surjective hEq⟩

def PrefixGlues (A : ℕ → Submodule R M) (x : ℕ → M) (n : ℕ) (w : M) : Prop :=
  ∀ i < n, w - x i ∈ A i

def prefixKernel (A : ℕ → Submodule R M) (n : ℕ) : Submodule R M :=
  ⨅ i : Fin n, A i

theorem mem_prefixKernel (A : ℕ → Submodule R M) (n : ℕ) (w : M) :
    w ∈ prefixKernel A n ↔ ∀ i < n, w ∈ A i := by
  simp only [prefixKernel, Submodule.mem_iInf]
  exact ⟨fun h i hi => h ⟨i, hi⟩, fun h i => h i i.isLt⟩

theorem prefix_fiber {A : ℕ → Submodule R M} {x : ℕ → M} {n : ℕ} {w t : M}
    (hw : PrefixGlues A x n w) : PrefixGlues A x n t ↔ t - w ∈ prefixKernel A n := by
  rw [mem_prefixKernel]
  constructor
  · intro ht i hi
    convert (A i).sub_mem (ht i hi) (hw i hi) using 1 <;> abel
  · intro h i hi
    convert (A i).add_mem (h i hi) (hw i hi) using 1 <;> abel

/-- S6: defined only with an actual successful-PrefixGlues witness. -/
def stepClass (A : ℕ → Submodule R M) (x : ℕ → M) (n : ℕ)
    (w : {w : M // PrefixGlues A x n w}) : M ⧸ (prefixKernel A n ⊔ A n) :=
  Submodule.Quotient.mk (w.val - x n)

theorem step_independent (A : ℕ → Submodule R M) (x : ℕ → M) (n : ℕ)
    (w t : {w : M // PrefixGlues A x n w}) : stepClass A x n w = stepClass A x n t := by
  apply (Submodule.Quotient.eq _).mpr
  have h := (prefix_fiber t.property).mp w.property
  convert (show prefixKernel A n ≤ prefixKernel A n ⊔ A n from le_sup_left) h using 1 <;> abel

theorem step_zero_iff (A : ℕ → Submodule R M) (x : ℕ → M) (n : ℕ)
    (w : {w : M // PrefixGlues A x n w}) :
    stepClass A x n w = 0 ↔ ∃ t, PrefixGlues A x (n + 1) t := by
  rw [stepClass, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    obtain ⟨u, hu, a, ha, hsum⟩ := Submodule.mem_sup.mp h
    refine ⟨w.val - u, ?_⟩
    intro i hi
    by_cases hin : i < n
    · have hu' := (mem_prefixKernel A n u).mp hu i hin
      convert (A i).sub_mem (w.property i hin) hu' using 1 <;> abel
    · have : i = n := by omega
      subst i
      have he : w.val - u - x n = a := by
        calc
          _ = (w.val - x n) - u := by abel
          _ = (u + a) - u := by rw [← hsum]
          _ = a := by abel
      simpa only [he] using ha
  · rintro ⟨t, ht⟩
    have ht' : PrefixGlues A x n t := fun i hi => ht i (by omega)
    have hw := (prefix_fiber ht').mp w.property
    convert (prefixKernel A n ⊔ A n).add_mem
      ((show prefixKernel A n ≤ prefixKernel A n ⊔ A n from le_sup_left) hw)
      ((show A n ≤ prefixKernel A n ⊔ A n from le_sup_right) (ht n (by omega))) using 1 <;> abel

theorem prefix_exists (A : ℕ → Submodule R M) (x : ℕ → M) (n : ℕ)
    (hpair : ∀ i < n, ∀ j < n, x i - x j ∈ A i ⊔ A j)
    (hdistrib : ∀ m, 0 < m → m < n →
      prefixKernel A m ⊔ A m = ⨅ i : Fin m, (A i ⊔ A m)) :
    ∃ w, PrefixGlues A x n w := by
  induction n with
  | zero => exact ⟨0, fun i hi => by omega⟩
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        refine ⟨x 0, ?_⟩
        intro i hi
        have : i = 0 := by omega
        subst i
        simp
      obtain ⟨w, hw⟩ := ih (fun i hi j hj => hpair i (by omega) j (by omega))
        (fun m hm hmn => hdistrib m hm (by omega))
      apply (step_zero_iff A x n ⟨w, hw⟩).mp
      rw [stepClass, Submodule.Quotient.mk_eq_zero, hdistrib n (by omega) (by omega)]
      simp only [Submodule.mem_iInf]
      intro i
      have h1 := (show A i ≤ A i ⊔ A n from le_sup_left) (hw i i.isLt)
      have h2 := hpair i (by omega) n (by omega)
      convert (A i ⊔ A n).add_mem h1 h2 using 1 <;> abel

/-- The recursive test uses every possible PrefixGlues representative, all equivalent by independence. -/
theorem all_steps_iff (A : ℕ → Submodule R M) (x : ℕ → M) (n : ℕ) :
    (∃ w, PrefixGlues A x n w) ↔
      ∀ m < n, ∀ w : {w : M // PrefixGlues A x m w}, stepClass A x m w = 0 := by
  constructor
  · rintro ⟨t, ht⟩ m hm w
    exact (step_zero_iff A x m w).mpr ⟨t, fun i hi => ht i (by omega)⟩
  · intro h
    induction n with
    | zero => exact ⟨0, fun i hi => by omega⟩
    | succ n ih =>
        obtain ⟨w, hw⟩ := ih (fun m hm => h m (by omega))
        exact (step_zero_iff A x n ⟨w, hw⟩).mp (h n (by omega) ⟨w, hw⟩)

theorem permutation_invariant {J K : Type*} (e : J ≃ K)
    (A : K → Submodule R M) (x : K → M) (t : M) :
    (∀ j, t - x (e j) ∈ A (e j)) ↔ ∀ k, t - x k ∈ A k :=
  by
    constructor
    · intro h k
      simpa using h (e.symm k)
    · intro h j
      exact h (e j)

/- S5: the actual four rational hyperplanes and affine records. -/
abbrev V := Fin 3 → ℚ

def form4 : Fin 4 → V →ₗ[ℚ] ℚ := ![
  (LinearMap.proj 0 : V →ₗ[ℚ] ℚ), (LinearMap.proj 1 : V →ₗ[ℚ] ℚ), (LinearMap.proj 2 : V →ₗ[ℚ] ℚ),
  (LinearMap.proj 0 : V →ₗ[ℚ] ℚ) + (LinearMap.proj 1 : V →ₗ[ℚ] ℚ) + (LinearMap.proj 2 : V →ₗ[ℚ] ℚ)]

def spaces4 (i : Fin 4) : Submodule ℚ V := (form4 i).ker
def records4 : Fin 4 → V := ![0, 0, 0, ![1, 0, 0]]
def omitWitness : Fin 4 → V := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], 0]

theorem every_triple (j : Fin 4) :
    ∀ i : Fin 4, i ≠ j → omitWitness j - records4 i ∈ spaces4 i := by
  intro i hij
  fin_cases j <;> fin_cases i <;> norm_num [spaces4, form4, omitWitness, records4,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.proj_apply,
    Matrix.cons_val, Fin.reduceFinMk] at * <;>
    norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail]

theorem not_all_four : ¬ ∃ t : V, ∀ i : Fin 4, t - records4 i ∈ spaces4 i := by
  rintro ⟨t, ht⟩
  have h0 := ht 0
  have h1 := ht 1
  have h2 := ht 2
  have h3 := ht 3
  change t 0 - 0 = 0 at h0
  change t 1 - 0 = 0 at h1
  change t 2 - 0 = 0 at h2
  change (t 0 - 1) + (t 1 - 0) + (t 2 - 0) = 0 at h3
  linarith

/-- Different first records really give different intermediate intersections. -/
theorem intermediate_kernel_can_change :
    (⊥ : Submodule ℚ ℚ) ≠ ⊤ := by
  intro h
  have : (1 : ℚ) ∈ (⊥ : Submodule ℚ ℚ) := by rw [h]; trivial
  simpa using this

theorem prefix_kernel_one (A : ℕ → Submodule R M) : prefixKernel A 1 = A 0 := by
  ext x
  rw [mem_prefixKernel]
  constructor
  · exact fun h => h 0 (by omega)
  · intro h i hi
    have : i = 0 := by omega
    simpa only [this] using h


end MathGauge.GR101
