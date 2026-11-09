import Bounds

noncomputable section
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
open formal_oet.vol_01.ch_01_foundations
namespace HCH02
variable {X I : Type} [Fintype I] {bot : X}

abbrev Step (X I : Type) (bot : X) := Operator X bot × Mat I

def run : List (Step X I bot) → Operator X bot
  | [] => ident
  | p :: ps => comp (run ps) p.1

def stage : List (Step X I bot) → Set X → ℕ → Set X
  | _, U, 0 => U
  | [], U, _ + 1 => U
  | p :: ps, U, m + 1 => stage ps (p.1.func '' U) m

theorem stage_succ (ps : List (Step X I bot)) (U : Set X) (m : ℕ) (hm : m < ps.length) :
    stage ps U (m + 1) = (ps[m]).1.func '' stage ps U m := by
  induction ps generalizing U m with
  | nil => simp at hm
  | cons p ps ih =>
    cases m with
    | zero => simp [stage]
    | succ m => simpa [stage] using ih (p.1.func '' U) m (by simpa using hm)

theorem stage_eq_image_take (ps : List (Step X I bot)) (U : Set X) (m : ℕ) :
    stage ps U m = (run (ps.take m)).func '' U := by
  induction ps generalizing U m with
  | nil => cases m <;> simp [stage, run, ident]
  | cons p ps ih =>
    cases m with
    | zero => simp [stage, run, ident]
    | succ m => simpa [stage, run, comp, Set.image_image] using ih (p.1.func '' U) m

theorem final_image (ps : List (Step X I bot)) (U : Set X) :
    stage ps U ps.length = (run ps).func '' U := by
  rw [stage_eq_image_take, List.take_length]

theorem run_domain_split (p : Step X I bot) (ps : List (Step X I bot)) {U : Set X}
    (hU : U ⊆ dom (run (p :: ps))) :
    U ⊆ dom p.1 ∧ p.1.func '' U ⊆ dom (run ps) := by
  simp only [run, dom_comp, Set.subset_def, Set.mem_setOf_eq] at hU
  refine ⟨fun x hx => (hU x hx).1, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (hU x hx).2

theorem stage_domain (ps : List (Step X I bot)) {U : Set X}
    (hU : U ⊆ dom (run ps)) :
    ∀ m (hm : m < ps.length), stage ps U m ⊆ dom (ps[m]).1 := by
  induction ps generalizing U with
  | nil => simp
  | cons p ps ih =>
    have hs := run_domain_split p ps hU
    intro m hm
    cases m with
    | zero => simpa [stage] using hs.1
    | succ m => simpa [stage] using ih hs.2 m (by simpa using hm)

def AllSteps (P : Operator X bot → Mat I → Set X → Prop) :
    List (Step X I bot) → Set X → Prop
  | [], _ => True
  | p :: ps, U => P p.1 p.2 U ∧ AllSteps P ps (p.1.func '' U)

theorem allSteps_iff (P : Operator X bot → Mat I → Set X → Prop)
    (ps : List (Step X I bot)) (U : Set X) :
    AllSteps P ps U ↔ ∀ m (hm : m < ps.length), P (ps[m]).1 (ps[m]).2 (stage ps U m) := by
  induction ps generalizing U with
  | nil => simp [AllSteps]
  | cons p ps ih =>
    rw [AllSteps, ih]
    constructor
    · rintro ⟨h, hs⟩ m hm
      cases m with
      | zero => simpa [stage] using h
      | succ m => simpa [stage] using hs m (by simpa using hm)
    · intro h
      constructor
      · simpa [stage] using h 0 (by simp)
      · intro m hm
        simpa [stage] using h (m + 1) (by simpa using hm)

def matrices (ps : List (Step X I bot)) : List (Mat I) := ps.map Prod.snd

theorem chain_lip {d : I → X → X → ENNReal} (ps : List (Step X I bot)) {U : Set X}
    (hU : U ⊆ dom (run ps)) (hs : AllSteps (fun φ M V => M ∈ Lip d φ V) ps U) :
    product (matrices ps) ∈ Lip d (run ps) U := by
  induction ps generalizing U with
  | nil => exact lip_ident hU
  | cons p ps ih =>
    exact lip_comp hU hs.1 (ih (run_domain_split p ps hU).2 hs.2)

theorem chain_colip_aux {d : I → X → X → ENNReal} (ps : List (Step X I bot)) {U : Set X}
    (hne : U.Nonempty) (hU : U ⊆ dom (run ps))
    (hs : AllSteps (fun φ M V => M ∈ CoLip d φ V) ps U) :
    product (matrices ps) ∈ CoLip d (run ps) U := by
  induction ps generalizing U with
  | nil => exact colip_ident hne hU
  | cons p ps ih =>
    exact colip_comp hU hs.1
      (ih (hne.image p.1.func) (run_domain_split p ps hU).2 hs.2)

theorem chain_colip {d : I → X → X → ENNReal} (ps : List (Step X I bot)) {U : Set X}
    (hpos : ps ≠ []) (hU : U ⊆ dom (run ps))
    (hs : AllSteps (fun φ M V => M ∈ CoLip d φ V) ps U) :
    product (matrices ps) ∈ CoLip d (run ps) U := by
  cases ps with
  | nil => exact (hpos rfl).elim
  | cons p ps => exact chain_colip_aux (p :: ps) hs.1.1 hU hs

theorem chain_lip_from_local {d : I → X → X → ENNReal} (ps : List (Step X I bot))
    {U : Set X} (hU : U ⊆ dom (run ps))
    (hs : ∀ m (hm : m < ps.length), (ps[m]).2 ∈ Lip d (ps[m]).1 (stage ps U m)) :
    product (matrices ps) ∈ Lip d (run ps) U :=
  chain_lip ps hU ((allSteps_iff _ ps U).mpr hs)

theorem chain_colip_from_local {d : I → X → X → ENNReal} (ps : List (Step X I bot))
    {U : Set X} (hpos : ps ≠ []) (hU : U ⊆ dom (run ps))
    (hs : ∀ m (hm : m < ps.length), (ps[m]).2 ∈ CoLip d (ps[m]).1 (stage ps U m)) :
    product (matrices ps) ∈ CoLip d (run ps) U :=
  chain_colip ps hpos hU ((allSteps_iff _ ps U).mpr hs)

end HCH02
