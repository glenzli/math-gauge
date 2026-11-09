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
