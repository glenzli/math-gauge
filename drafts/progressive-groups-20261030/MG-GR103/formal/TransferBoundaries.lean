import BlockFixedPoints

namespace MathGauge.GR103

variable {A B : Type*} [CompleteLattice A] [CompleteLattice B]

/-- S3: the forward lax inequality uses the actual right adjoint. -/
theorem forward_lax (T : A →o A) (U : B →o B) (α : A →o B) (γ : B →o A)
    (adj : GaloisConnection α γ) (h : ∀ x, α (T x) ≤ U (α x)) :
    α T.lfp ≤ U.lfp := by
  apply (adj _ _).mpr
  apply T.lfp_le
  apply (adj _ _).mp
  exact (h _).trans ((U.monotone (adj.l_u_le _)).trans U.map_lfp.le)

/-- The reverse comparison needs no adjoint. -/
theorem reverse_lax (T : A →o A) (U : B →o B) (α : A →o B)
    (h : ∀ x, U (α x) ≤ α (T x)) : U.lfp ≤ α T.lfp := by
  apply U.lfp_le
  simpa only [T.map_lfp] using h T.lfp

theorem semiconjugacy_comparison (T : A →o A) (U : B →o B) (α : A →o B)
    (h : ∀ x, α (T x) = U (α x)) : U.lfp ≤ α T.lfp :=
  reverse_lax T U α (fun x => (h x).symm.le)

theorem const_lfp (a : A) : (OrderHom.const A a).lfp = a :=
  (OrderHom.const A a).map_lfp.symm

theorem strict_forward_finite :
    GaloisConnection (OrderHom.id : Bool →o Bool) OrderHom.id ∧
    (∀ x : Bool, (OrderHom.const Bool false) x ≤ (OrderHom.const Bool true) x) ∧
    (OrderHom.const Bool false).lfp < (OrderHom.const Bool true).lfp := by
  refine ⟨fun _ _ => Iff.rfl, fun _ => show false ≤ true from by decide, ?_⟩
  rw [const_lfp, const_lfp]
  decide

theorem strict_reverse_finite :
    let T := OrderHom.const Bool true
    let U := OrderHom.const Bool false
    let α : Bool →o Bool := OrderHom.id
    GaloisConnection α OrderHom.id ∧
    (∀ x : Bool, U (α x) ≤ α (T x)) ∧ U.lfp < α T.lfp :=
  strict_forward_finite

theorem identity_lfp : (OrderHom.id : A →o A).lfp = ⊥ :=
  le_antisymm ((OrderHom.id : A →o A).lfp_le le_rfl) bot_le

/-- S4 uses the two-element lattice, identity dynamics and a constant-top map. -/
theorem monotone_semiconjugacy_not_exact :
    (∀ x : Bool, (OrderHom.const Bool true) ((OrderHom.id : Bool →o Bool) x) =
      (OrderHom.id : Bool →o Bool) ((OrderHom.const Bool true) x)) ∧
    (OrderHom.const Bool true) (OrderHom.id : Bool →o Bool).lfp ≠
      (OrderHom.id : Bool →o Bool).lfp ∧
    ¬ ∃ γ : Bool →o Bool, GaloisConnection (OrderHom.const Bool true) γ := by
  refine ⟨fun _ => rfl, ?_, ?_⟩
  · rw [identity_lfp]
    decide
  · rintro ⟨γ, hγ⟩
    have h := (hγ false false).mpr (show false ≤ γ false from bot_le)
    contradiction

/-- The hypothesis is exactly preservation of increasing countable suprema. -/
def PreservesOmega (f : A → B) : Prop :=
  ∀ x : ℕ → A, Monotone x → f (⨆ n, x n) = ⨆ n, f (x n)

def approximant (T : A →o A) : ℕ → A
  | 0 => ⊥
  | n + 1 => T (approximant T n)

def omegaStage (T : A →o A) : A := ⨆ n, approximant T n

theorem approximant_increasing (T : A →o A) : Monotone (approximant T) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => exact bot_le
  | succ n ih => exact T.monotone ih

theorem approximant_le_prefixed (T : A →o A) (a : A) (ha : T a ≤ a) (n : ℕ) :
    approximant T n ≤ a := by
  induction n with
  | zero => exact bot_le
  | succ n ih => exact (T.monotone ih).trans ha

theorem omega_le_lfp (T : A →o A) : omegaStage T ≤ T.lfp :=
  iSup_le fun n => approximant_le_prefixed T _ T.map_lfp.le n

theorem omega_le_update (T : A →o A) : omegaStage T ≤ T (omegaStage T) := by
  apply iSup_le
  intro n
  cases n with
  | zero => exact bot_le
  | succ n => exact T.monotone (le_iSup (approximant T) n)

theorem omega_eq_lfp_iff (T : A →o A) :
    omegaStage T = T.lfp ↔ T (omegaStage T) ≤ omegaStage T := by
  constructor
  · intro h
    rw [h, T.map_lfp]
  · intro h
    exact le_antisymm (omega_le_lfp T) (T.lfp_le h)

theorem kleene (T : A →o A) (hT : PreservesOmega T) : omegaStage T = T.lfp := by
  apply (omega_eq_lfp_iff T).mpr
  rw [omegaStage, hT _ (approximant_increasing T)]
  exact iSup_le fun n => le_iSup (approximant T) (n + 1)

theorem iterate_transport (T : A →o A) (U : B →o B) (α : A →o B)
    (hbot : α ⊥ = ⊥) (hcomm : ∀ x, α (T x) = U (α x)) (n : ℕ) :
    α (approximant T n) = approximant U n := by
  induction n with
  | zero => exact hbot
  | succ n ih => simpa only [approximant, hcomm, ih]

theorem omega_transport (T : A →o A) (U : B →o B) (α : A →o B)
    (hT : PreservesOmega T) (hU : PreservesOmega U) (hα : PreservesOmega α)
    (hbot : α ⊥ = ⊥) (hcomm : ∀ x, α (T x) = U (α x)) :
    α T.lfp = U.lfp := by
  rw [← kleene T hT, ← kleene U hU]
  unfold omegaStage
  rw [hα _ (approximant_increasing T)]
  exact congrArg iSup (funext (iterate_transport T U α hbot hcomm))

/-- S6: naturals are `some n`; `none` is the extra point ω, not a natural index. -/
def jump : Set (Option ℕ) →o Set (Option ℕ) where
  toFun s := {x | match x with
    | some n => n = 0 ∨ ∃ k, n = k + 1 ∧ some k ∈ s
    | none => ∀ n, some n ∈ s}
  monotone' s t h x hx := by
    cases x with
    | none => exact fun n => h (hx n)
    | some n => rcases hx with hz | ⟨k, hk, hs⟩
                · exact Or.inl hz
                · exact Or.inr ⟨k, hk, h hs⟩

def initialSegment (n : ℕ) : Set (Option ℕ) := {x | ∃ k < n, x = some k}

theorem jump_segment (n : ℕ) : jump (initialSegment n) = initialSegment (n + 1) := by
  ext x
  cases x with
  | none =>
      simp only [jump, OrderHom.coe_mk, Set.mem_setOf_eq, initialSegment]
      constructor
      · intro h
        obtain ⟨k, hk, he⟩ := h n
        have : n = k := Option.some.inj he
        omega
      · rintro ⟨k, _, h⟩
        cases h
  | some k =>
      simp only [jump, OrderHom.coe_mk, Set.mem_setOf_eq, initialSegment, Option.some.injEq]
      constructor
      · rintro (hz | ⟨j, hj, l, hl, h⟩)
        · exact ⟨k, by omega, rfl⟩
        · exact ⟨k, by omega, rfl⟩
      · rintro ⟨l, hl, he⟩
        by_cases hk : k = 0
        · exact Or.inl hk
        · exact Or.inr ⟨k - 1, by omega, k - 1, by omega, rfl⟩

theorem jump_iterates (n : ℕ) : approximant jump n = initialSegment n := by
  induction n with
  | zero => ext x; simp [approximant, initialSegment]
  | succ n ih => simpa only [approximant, ih] using jump_segment n

theorem jump_omega : omegaStage jump = Set.range (some : ℕ → Option ℕ) := by
  ext x
  simp only [omegaStage, Set.iSup_eq_iUnion, Set.mem_iUnion, jump_iterates,
    initialSegment, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, k, _, hx⟩
    exact ⟨k, hx.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, k, by omega, rfl⟩

theorem jump_lfp : jump.lfp = Set.univ := by
  have hn : ∀ n, some n ∈ jump.lfp := by
    intro n
    exact omega_le_lfp jump (by rw [jump_omega]; exact ⟨n, rfl⟩)
  apply Set.eq_univ_of_forall
  intro x
  cases x with
  | some n => exact hn n
  | none => have h : none ∈ jump jump.lfp := hn
            simpa only [jump.map_lfp] using h

theorem jump_omega_not_lfp : omegaStage jump ≠ jump.lfp := by
  rw [jump_omega, jump_lfp]
  intro h
  have : none ∈ Set.range (some : ℕ → Option ℕ) := by rw [h]; trivial
  simpa using this

theorem jump_not_omega_continuous : ¬ PreservesOmega jump := by
  intro h
  exact jump_omega_not_lfp (kleene jump h)

/-- Equality for a concrete pair of constant systems needs neither general mechanism. -/
theorem constant_system_transport (α : A →o B) (a : A) :
    α (OrderHom.const A a).lfp = (OrderHom.const B (α a)).lfp := by
  rw [const_lfp, const_lfp]

end MathGauge.GR103
