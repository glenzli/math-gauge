import Core

noncomputable section
namespace MathGauge.RecursiveClosure.System
variable {Y V E I : Type} [Fintype I] {g : Gauge Y I}

def InfoLE (a b : Option Y) : Prop := a = none ∨ a = b
theorem info_refl (a : Option Y) : InfoLE a a := Or.inr rfl
theorem info_trans {a b c : Option Y} (h : InfoLE a b) (k : InfoLE b c) : InfoLE a c := by
  rcases h with h|h
  · exact Or.inl h
  · subst a; exact k

theorem partial_mono (s : System Y V E I g) {F G : s.PartialFamily}
    (h : ∀ v x, InfoLE (F v x) (G v x)) :
    ∀ v x, InfoLE (s.partialTransform F v x) (s.partialTransform G v x) := by
  intro v x
  cases hs : s.step v x with
  | inl y => exact Or.inr (by simp [partialTransform,hs])
  | inr ez =>
    rcases ez with ⟨e,z⟩
    rcases h (s.dst e) z with hz|hz
    · exact Or.inl (by simp [partialTransform,hs,hz])
    · exact Or.inr (by simp [partialTransform,hs,hz])

def eval (s : System Y V E I g) : ℕ → s.PartialFamily
  | 0 => fun _ _ => none
  | n+1 => s.partialTransform (s.eval n)

theorem eval_mono_step (s : System Y V E I g) (n : ℕ) :
    ∀ v x, InfoLE (s.eval n v x) (s.eval (n+1) v x) := by
  induction n with
  | zero => intros; exact Or.inl rfl
  | succ n ih => exact s.partial_mono ih

theorem eval_mono (s : System Y V E I g) {n m : ℕ} (h : n ≤ m) :
    ∀ v x, InfoLE (s.eval n v x) (s.eval m v x) := by
  induction m,h using Nat.le_induction with
  | base => intros; exact info_refl _
  | succ m h ih =>
    intro v x
    exact info_trans (ih v x) (s.eval_mono_step m v x)

theorem eval_unique (s : System Y V E I g) {v : V} {x : s.Input v}
    {n m : ℕ} {a b : Y} (ha : s.eval n v x = some a) (hb : s.eval m v x = some b) : a = b := by
  rcases le_total n m with h|h
  · have hh := s.eval_mono h v x
    simp [InfoLE,ha,hb] at hh
    exact hh
  · have hh := s.eval_mono h v x
    simp [InfoLE,ha,hb] at hh
    exact hh.symm

def least (s : System Y V E I g) : s.PartialFamily := by
  classical
  exact fun v x => if h : ∃ y, ∃ n, s.eval n v x = some y then some (Classical.choose h) else none

theorem least_some_iff (s : System Y V E I g) (v : V) (x : s.Input v) (y : Y) :
    s.least v x = some y ↔ ∃ n, s.eval n v x = some y := by
  classical
  unfold least
  split_ifs with h
  · constructor
    · intro he
      have he' : Classical.choose h = y := Option.some.inj he
      simpa [← he'] using Classical.choose_spec h
    · rintro ⟨n,hn⟩
      obtain ⟨m,hm⟩ := Classical.choose_spec h
      have := s.eval_unique hm hn
      simp [this]
  · constructor
    · simp
    · rintro ⟨n,hn⟩; exact (h ⟨y,n,hn⟩).elim

theorem least_none_iff (s : System Y V E I g) (v : V) (x : s.Input v) :
    s.least v x = none ↔ ∀ n, s.eval n v x = none := by
  constructor
  · intro hl n
    cases h : s.eval n v x with
    | none => rfl
    | some y => have := (s.least_some_iff v x y).2 ⟨n,h⟩; simp [hl] at this
  · intro h
    cases hl : s.least v x with
    | none => rfl
    | some y => obtain ⟨n,hn⟩ := (s.least_some_iff v x y).1 hl; simp [h n] at hn

theorem least_fixed (s : System Y V E I g) : s.partialTransform s.least = s.least := by
  funext v x
  cases hs : s.step v x with
  | inl y =>
    have hl : s.least v x = some y := (s.least_some_iff v x y).2 ⟨1,by simp [eval,partialTransform,hs]⟩
    simp [partialTransform,hs,hl]
  | inr ez =>
    rcases ez with ⟨e,z⟩
    cases hz : s.least (s.dst e) z with
    | none =>
      have hn := (s.least_none_iff _ _).1 hz
      have hl : s.least v x = none := (s.least_none_iff v x).2 (by
        intro n; cases n with
        | zero => rfl
        | succ n => simp [eval,partialTransform,hs,hn n])
      simp [partialTransform,hs,hz,hl]
    | some y =>
      obtain ⟨n,hn⟩ := (s.least_some_iff _ _ y).1 hz
      have hl : s.least v x = some (s.ret e y) := (s.least_some_iff _ _ _).2
        ⟨n+1,by simp [eval,partialTransform,hs,hn]⟩
      simp [partialTransform,hs,hz,hl]

theorem eval_le_fixed (s : System Y V E I g) (F : s.PartialFamily)
    (hf : s.partialTransform F = F) (n : ℕ) : ∀ v x, InfoLE (s.eval n v x) (F v x) := by
  induction n with
  | zero => intros; exact Or.inl rfl
  | succ n ih =>
    have := s.partial_mono ih
    simpa [eval,hf] using this

theorem least_le_fixed (s : System Y V E I g) (F : s.PartialFamily)
    (hf : s.partialTransform F = F) : ∀ v x, InfoLE (s.least v x) (F v x) := by
  intro v x
  cases hl : s.least v x with
  | none => exact Or.inl rfl
  | some y =>
    obtain ⟨n,hn⟩ := (s.least_some_iff _ _ _).1 hl
    simpa [hn] using s.eval_le_fixed F hf n v x

inductive Halts (s : System Y V E I g) : (v : V) → s.Input v → Prop
  | stop {v x y} : s.step v x = Sum.inl y → s.Halts v x
  | call {v x e z} : s.step v x = Sum.inr ⟨e,z⟩ → s.Halts (s.dst e) z → s.Halts v x

theorem halts_iff_evaluates (s : System Y V E I g) (v : V) (x : s.Input v) :
    s.Halts v x ↔ ∃ n y, s.eval n v x = some y := by
  constructor
  · intro h
    induction h with
    | @stop v x y hs => exact ⟨1,y,by simp [eval,partialTransform,hs]⟩
    | @call v x e z hs hh ih =>
      obtain ⟨n,y,hy⟩ := ih
      exact ⟨n+1,s.ret e y,by simp [eval,partialTransform,hs,hy]⟩
  · rintro ⟨n,y,hy⟩
    induction n generalizing v x y with
    | zero => simp [eval] at hy
    | succ n ih =>
      cases hs : s.step v x with
      | inl z => exact Halts.stop hs
      | inr ez =>
        rcases ez with ⟨e,z⟩
        cases he : s.eval n (s.dst e) z with
        | none => simp [eval,partialTransform,hs,he] at hy
        | some q => exact Halts.call hs (ih _ _ _ he)

theorem least_domain (s : System Y V E I g) (v : V) (x : s.Input v) :
    s.least v x ≠ none ↔ s.Halts v x := by
  rw [halts_iff_evaluates]
  constructor
  · intro h
    cases hl : s.least v x with
    | none => exact (h hl).elim
    | some y => obtain ⟨n,hn⟩ := (s.least_some_iff _ _ _).1 hl; exact ⟨n,y,hn⟩
  · rintro ⟨n,y,hy⟩ h
    have hn := (s.least_none_iff _ _).1 h n
    simp [hn] at hy

theorem iterate_stop (s : System Y V E I g) (H : s.Family) {v x y}
    (hs : s.step v x = Sum.inl y) (n : ℕ) : s.transform^[n+1] H v x = y := by
  rw [Function.iterate_succ_apply']
  simp [transform,hs]

theorem iterate_call (s : System Y V E I g) (H : s.Family) {v x e z}
    (hs : s.step v x = Sum.inr ⟨e,z⟩) (n : ℕ) :
    s.transform^[n+1] H v x = s.ret e (s.transform^[n] H (s.dst e) z) := by
  rw [Function.iterate_succ_apply']
  simp [transform,hs]

theorem eval_forces_unfold (s : System Y V E I g) (H : s.Family) {v x n y}
    (h : s.eval n v x = some y) : s.transform^[n] H v x = y := by
  induction n generalizing v x y with
  | zero => simp [eval] at h
  | succ n ih =>
    cases hs : s.step v x with
    | inl z =>
      have hz : z = y := by simpa [eval,partialTransform,hs] using h
      simpa [hz] using s.iterate_stop H hs n
    | inr ez =>
      rcases ez with ⟨e,z⟩
      cases he : s.eval n (s.dst e) z with
      | none => simp [eval,partialTransform,hs,he] at h
      | some q =>
        have hq : s.ret e q = y := by simpa [eval,partialTransform,hs,he] using h
        rw [s.iterate_call H hs n,ih he,hq]

theorem finite_stop_stable (s : System Y V E I g) (H : s.Family) {v x n y}
    (h : s.eval n v x = some y) {m : ℕ} (hm : n ≤ m) : s.transform^[m] H v x = y := by
  have hh := s.eval_mono hm v x
  have hx : s.eval m v x = some y := by
    rcases hh with hh|hh
    · simp [h] at hh
    · exact hh.symm.trans h
  exact s.eval_forces_unfold H hx

end MathGauge.RecursiveClosure.System
