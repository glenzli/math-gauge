import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

set_option linter.unnecessarySeqFocus false

namespace MathGauge.R101

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

def Compatible (A B C : Submodule R M) (x y z : M) : Prop :=
  x - y ∈ A ⊔ B ∧ x - z ∈ A ⊔ C ∧ y - z ∈ B ⊔ C

def PartialGlue (A B : Submodule R M) (x y w : M) : Prop :=
  w - x ∈ A ∧ w - y ∈ B

def Glues (A B C : Submodule R M) (x y z w : M) : Prop :=
  PartialGlue A B x y w ∧ w - z ∈ C

def ambiguity (A B C : Submodule R M) : Submodule R M := (A ⊓ B) ⊔ C

def obstruction_space (A B C : Submodule R M) : Submodule R M :=
  (A ⊔ C) ⊓ (B ⊔ C)

lemma partial_exists {A B : Submodule R M} {x y : M} (h : x - y ∈ A ⊔ B) :
    ∃ w, PartialGlue A B x y w := by
  rcases Submodule.mem_sup.mp h with ⟨a, ha, b, hb, hab⟩
  refine ⟨x - a, ?_, ?_⟩
  · convert A.neg_mem ha using 1 <;> abel
  · have heq : x - a - y = b := by
      calc
        x - a - y = (x - y) - a := by abel
        _ = (a + b) - a := by rw [← hab]
        _ = b := by abel
    simpa [heq] using hb

lemma partial_difference {A B : Submodule R M} {x y w w' : M}
    (h : PartialGlue A B x y w) (h' : PartialGlue A B x y w') :
    w - w' ∈ A ⊓ B := by
  constructor
  · convert A.sub_mem h.1 h'.1 using 1 <;> abel
  · convert B.sub_mem h.2 h'.2 using 1 <;> abel

lemma obstruction_mem {A B C : Submodule R M} {x y z w : M}
    (h : Compatible A B C x y z) (hw : PartialGlue A B x y w) :
    w - z ∈ obstruction_space A B C := by
  constructor
  · convert (A ⊔ C).add_mem (show w - x ∈ A ⊔ C from (show A ≤ A ⊔ C from le_sup_left) hw.1) h.2.1 using 1 <;> abel
  · convert (B ⊔ C).add_mem (show w - y ∈ B ⊔ C from (show B ≤ B ⊔ C from le_sup_left) hw.2) h.2.2 using 1 <;> abel

lemma obstruction_independent {A B C : Submodule R M} {x y z w w' : M}
    (hw : PartialGlue A B x y w) (hw' : PartialGlue A B x y w') :
    (Submodule.Quotient.mk (w - z) : M ⧸ ambiguity A B C) =
      Submodule.Quotient.mk (w' - z) := by
  apply (Submodule.Quotient.eq _).mpr
  convert (show w - w' ∈ ambiguity A B C from (show A ⊓ B ≤ ambiguity A B C from le_sup_left) (partial_difference hw hw')) using 1 <;> abel

lemma obstruction_zero_iff {A B C : Submodule R M} {x y z w : M}
    (hw : PartialGlue A B x y w) :
    w - z ∈ ambiguity A B C ↔ ∃ t, Glues A B C x y z t := by
  constructor
  · intro h
    rcases Submodule.mem_sup.mp h with ⟨u, hu, c, hc, heq⟩
    refine ⟨w - u, ⟨?_, ?_⟩, ?_⟩
    · convert A.sub_mem hw.1 hu.1 using 1 <;> abel
    · convert B.sub_mem hw.2 hu.2 using 1 <;> abel
    · have heq' : w - u - z = c := by
        calc
          w - u - z = (w - z) - u := by abel
          _ = (u + c) - u := by rw [← heq]
          _ = c := by abel
      simpa [heq'] using hc
  · rintro ⟨t, ht⟩
    have hd : w - t ∈ A ⊓ B := partial_difference hw ht.1
    convert (ambiguity A B C).add_mem ((show A ⊓ B ≤ ambiguity A B C from le_sup_left) hd)
      ((show C ≤ ambiguity A B C from le_sup_right) ht.2) using 1 <;> abel

lemma solution_fiber {A B C : Submodule R M} {x y z t s : M}
    (ht : Glues A B C x y z t) :
    Glues A B C x y z s ↔ s - t ∈ (A ⊓ B) ⊓ C := by
  constructor
  · intro hs
    refine ⟨partial_difference hs.1 ht.1, ?_⟩
    convert C.sub_mem hs.2 ht.2 using 1 <;> abel
  · rintro ⟨hab, hc⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · convert A.add_mem hab.1 ht.1.1 using 1 <;> abel
    · convert B.add_mem hab.2 ht.1.2 using 1 <;> abel
    · convert C.add_mem hc ht.2 using 1 <;> abel

/-- Actual module of pairwise compatible representatives. -/
def records (A B C : Submodule R M) : Submodule R (M × M × M) where
  carrier := {r | Compatible A B C r.1 r.2.1 r.2.2}
  zero_mem' := by simp [Compatible]
  add_mem' := by
    intro r s hr hs
    rcases hr with ⟨hr1, hr2, hr3⟩
    rcases hs with ⟨hs1, hs2, hs3⟩
    refine ⟨?_, ?_, ?_⟩
    · change r.1 + s.1 - (r.2.1 + s.2.1) ∈ A ⊔ B
      convert (A ⊔ B).add_mem hr1 hs1 using 1 <;> abel
    · change r.1 + s.1 - (r.2.2 + s.2.2) ∈ A ⊔ C
      convert (A ⊔ C).add_mem hr2 hs2 using 1 <;> abel
    · change r.2.1 + s.2.1 - (r.2.2 + s.2.2) ∈ B ⊔ C
      convert (B ⊔ C).add_mem hr3 hs3 using 1 <;> abel
  smul_mem' := by
    intro a r hr
    exact ⟨by simpa [smul_sub] using (A ⊔ B).smul_mem a hr.1,
      by simpa [smul_sub] using (A ⊔ C).smul_mem a hr.2.1,
      by simpa [smul_sub] using (B ⊔ C).smul_mem a hr.2.2⟩

noncomputable def partial_choice {A B C : Submodule R M} (r : records A B C) : M :=
  Classical.choose (partial_exists r.property.1)

lemma partial_choice_spec {A B C : Submodule R M} (r : records A B C) :
    PartialGlue A B r.val.1 r.val.2.1 (partial_choice r) :=
  Classical.choose_spec (partial_exists r.property.1)

noncomputable def raw_obstruction (A B C : Submodule R M) :
    records A B C →ₗ[R] M ⧸ ambiguity A B C where
  toFun r := Submodule.Quotient.mk (partial_choice r - r.val.2.2)
  map_add' r s := by
    have hw : PartialGlue A B (r + s).val.1 (r + s).val.2.1
        (partial_choice r + partial_choice s) := by
      constructor
      · convert A.add_mem (partial_choice_spec r).1 (partial_choice_spec s).1 using 1 <;> simp only [Submodule.coe_add, Prod.fst_add] <;> abel
      · convert B.add_mem (partial_choice_spec r).2 (partial_choice_spec s).2 using 1 <;> simp only [Submodule.coe_add, Prod.snd_add, Prod.fst_add] <;> abel
    rw [obstruction_independent (partial_choice_spec (r + s)) hw]
    change Submodule.Quotient.mk (partial_choice r + partial_choice s - (r.val.2.2 + s.val.2.2)) = _
    rw [show partial_choice r + partial_choice s - (r.val.2.2 + s.val.2.2) =
        (partial_choice r - r.val.2.2) + (partial_choice s - s.val.2.2) by abel]
    rfl
  map_smul' a r := by
    have hw : PartialGlue A B (a • r).val.1 (a • r).val.2.1 (a • partial_choice r) :=
      ⟨by simpa [smul_sub] using A.smul_mem a (partial_choice_spec r).1,
       by simpa [smul_sub] using B.smul_mem a (partial_choice_spec r).2⟩
    rw [obstruction_independent (partial_choice_spec (a • r)) hw]
    change Submodule.Quotient.mk (a • partial_choice r - a • r.val.2.2) = _
    rw [← smul_sub]
    rfl

lemma raw_obstruction_eq {A B C : Submodule R M} (r : records A B C) {w : M}
    (hw : PartialGlue A B r.val.1 r.val.2.1 w) :
    raw_obstruction A B C r = Submodule.Quotient.mk (w - r.val.2.2) :=
  obstruction_independent (partial_choice_spec r) hw

lemma raw_zero_iff {A B C : Submodule R M} (r : records A B C) :
    raw_obstruction A B C r = 0 ↔ ∃ t, Glues A B C r.val.1 r.val.2.1 r.val.2.2 t := by
  change (Submodule.Quotient.mk (partial_choice r - r.val.2.2) : M ⧸ ambiguity A B C) =
    Submodule.Quotient.mk 0 ↔ _
  rw [Submodule.Quotient.eq, sub_zero]
  exact obstruction_zero_iff (partial_choice_spec r)

/-- Changes of representatives in A, B, and C form a genuine submodule of records. -/
def noise (A B C : Submodule R M) : Submodule R (records A B C) where
  carrier := {r | r.val.1 ∈ A ∧ r.val.2.1 ∈ B ∧ r.val.2.2 ∈ C}
  zero_mem' := by simp
  add_mem' := by
    intro r s hr hs
    exact ⟨A.add_mem hr.1 hs.1, B.add_mem hr.2.1 hs.2.1, C.add_mem hr.2.2 hs.2.2⟩
  smul_mem' := by
    intro a r hr
    exact ⟨A.smul_mem a hr.1, B.smul_mem a hr.2.1, C.smul_mem a hr.2.2⟩

lemma noise_in_kernel (A B C : Submodule R M) : noise A B C ≤ (raw_obstruction A B C).ker := by
  intro r hr
  apply (raw_zero_iff r).mpr
  refine ⟨0, ⟨?_, ?_⟩, ?_⟩
  · simpa using A.neg_mem hr.1
  · simpa using B.neg_mem hr.2.1
  · simpa using C.neg_mem hr.2.2

/-- Obstruction on actual residue records, with independent coordinate representatives identified. -/
noncomputable def obstruction (A B C : Submodule R M) :
    (records A B C ⧸ noise A B C) →ₗ[R] M ⧸ ambiguity A B C :=
  (noise A B C).liftQ (raw_obstruction A B C) (noise_in_kernel A B C)

lemma obstruction_on_record {A B C : Submodule R M} (r : records A B C) {w : M}
    (hw : PartialGlue A B r.val.1 r.val.2.1 w) :
    obstruction A B C (Submodule.Quotient.mk r) = Submodule.Quotient.mk (w - r.val.2.2) :=
  raw_obstruction_eq r hw

lemma obstruction_zero_on_record {A B C : Submodule R M} (r : records A B C) :
    obstruction A B C (Submodule.Quotient.mk r) = 0 ↔
      ∃ t, Glues A B C r.val.1 r.val.2.1 r.val.2.2 t :=
  raw_zero_iff r

/-- The exact range is the image of (A+C)∩(B+C) in the obstruction quotient. -/
theorem obstruction_range (A B C : Submodule R M) :
    (obstruction A B C).range =
      (obstruction_space A B C).map (ambiguity A B C).mkQ := by
  ext q
  constructor
  · rintro ⟨r, rfl⟩
    induction r using Submodule.Quotient.induction_on with
    | H r =>
      exact ⟨partial_choice r - r.val.2.2,
        obstruction_mem r.property (partial_choice_spec r), rfl⟩
  · rintro ⟨h, hh, rfl⟩
    let r : records A B C := ⟨(0, 0, -h), by
      exact ⟨by simp, by simpa using hh.1, by simpa using hh.2⟩⟩
    refine ⟨Submodule.Quotient.mk r, ?_⟩
    have hw : PartialGlue A B r.val.1 r.val.2.1 0 := by simp [r, PartialGlue]
    rw [obstruction_on_record r hw]
    simp [r]

def diagonal (A B C : Submodule R M) : M →ₗ[R] records A B C where
  toFun x := ⟨(x, x, x), by simp [records, Compatible]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def residue_map (A B C : Submodule R M) : M →ₗ[R] (records A B C ⧸ noise A B C) :=
  (noise A B C).mkQ.comp (diagonal A B C)

lemma residue_kernel (A B C : Submodule R M) :
    (residue_map A B C).ker = (A ⊓ B) ⊓ C := by
  ext x
  change (Submodule.Quotient.mk (diagonal A B C x) : records A B C ⧸ noise A B C) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change (x ∈ A ∧ x ∈ B ∧ x ∈ C) ↔ (x ∈ A ∧ x ∈ B) ∧ x ∈ C
  tauto

noncomputable def residue_embedding (A B C : Submodule R M) :
    (M ⧸ ((A ⊓ B) ⊓ C)) →ₗ[R] (records A B C ⧸ noise A B C) :=
  (((A ⊓ B) ⊓ C).liftQ (residue_map A B C) (by rw [residue_kernel]))

lemma residue_embedding_injective (A B C : Submodule R M) :
    Function.Injective (residue_embedding A B C) := by
  rw [← LinearMap.ker_eq_bot]
  apply eq_bot_iff.mpr
  intro q hq
  induction q using Submodule.Quotient.induction_on with
  | H x =>
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    have hx : x ∈ (residue_map A B C).ker := hq
    rwa [residue_kernel] at hx

lemma same_record_iff {A B C : Submodule R M} (r : records A B C) (t : M) :
    (Submodule.Quotient.mk r : records A B C ⧸ noise A B C) = residue_map A B C t ↔
      Glues A B C r.val.1 r.val.2.1 r.val.2.2 t := by
  change Submodule.Quotient.mk r = Submodule.Quotient.mk (diagonal A B C t) ↔ _
  rw [Submodule.Quotient.eq]
  change (r.val.1 - t ∈ A ∧ r.val.2.1 - t ∈ B ∧ r.val.2.2 - t ∈ C) ↔ _
  constructor
  · rintro ⟨ha, hb, hc⟩
    exact ⟨⟨by simpa using A.neg_mem ha, by simpa using B.neg_mem hb⟩,
      by simpa using C.neg_mem hc⟩
  · rintro ⟨⟨ha, hb⟩, hc⟩
    exact ⟨by simpa using A.neg_mem ha, by simpa using B.neg_mem hb,
      by simpa using C.neg_mem hc⟩

lemma obstruction_exact (A B C : Submodule R M) :
    (obstruction A B C).ker = (residue_embedding A B C).range := by
  ext q
  induction q using Submodule.Quotient.induction_on with
  | H r =>
    constructor
    · intro hr
      rcases (obstruction_zero_on_record r).mp hr with ⟨t, ht⟩
      exact ⟨Submodule.Quotient.mk t, ((same_record_iff r t).mpr ht).symm⟩
    · rintro ⟨z, hz⟩
      induction z using Submodule.Quotient.induction_on with
      | H t =>
        apply (obstruction_zero_on_record r).mpr
        exact ⟨t, (same_record_iff r t).mp hz.symm⟩

def obstruction_image (A B C : Submodule R M) : Submodule R (M ⧸ ambiguity A B C) :=
  (obstruction_space A B C).map (ambiguity A B C).mkQ

noncomputable def obstruction_onto (A B C : Submodule R M) :
    (records A B C ⧸ noise A B C) →ₗ[R] obstruction_image A B C :=
  (obstruction A B C).codRestrict (obstruction_image A B C) (by
    intro x
    rw [obstruction_image, ← obstruction_range]
    exact ⟨x, rfl⟩)

lemma obstruction_surjective (A B C : Submodule R M) :
    Function.Surjective (obstruction_onto A B C) := by
  intro q
  have hq : q.val ∈ (obstruction A B C).range := by
    rw [obstruction_range]
    exact q.property
  rcases hq with ⟨r, hr⟩
  exact ⟨r, Subtype.ext hr⟩

lemma obstruction_onto_exact (A B C : Submodule R M) :
    (obstruction_onto A B C).ker = (residue_embedding A B C).range := by
  rw [← obstruction_exact]
  ext q
  change obstruction_onto A B C q = 0 ↔ obstruction A B C q = 0
  exact Subtype.ext_iff

def elementary_record (A B C : Submodule R M) (h : obstruction_space A B C) : records A B C :=
  ⟨(0, 0, -h.val), by exact ⟨by simp, by simpa using h.property.1, by simpa using h.property.2⟩⟩

lemma obstruction_normalization (A B C : Submodule R M) (h : obstruction_space A B C) :
    (obstruction_onto A B C (Submodule.Quotient.mk (elementary_record A B C h))).val =
      (ambiguity A B C).mkQ h.val := by
  change obstruction A B C (Submodule.Quotient.mk (elementary_record A B C h)) = _
  rw [obstruction_on_record _ (show PartialGlue A B 0 0 0 from by simp [PartialGlue])]
  simp [elementary_record]

lemma record_equality {A B C : Submodule R M} (r s : records A B C) :
    (Submodule.Quotient.mk r : records A B C ⧸ noise A B C) = Submodule.Quotient.mk s ↔
      r.val.1 - s.val.1 ∈ A ∧ r.val.2.1 - s.val.2.1 ∈ B ∧ r.val.2.2 - s.val.2.2 ∈ C := by
  rw [Submodule.Quotient.eq]
  rfl

end MathGauge.R101
