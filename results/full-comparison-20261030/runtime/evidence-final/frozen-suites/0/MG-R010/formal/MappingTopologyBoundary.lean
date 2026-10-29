import MappingNaturality
import Mathlib.Data.Set.Countable
import Mathlib.Topology.DiscreteSubset

noncomputable section
open TopologicalSpace Topology Set CategoryTheory Opposite
universe u
namespace MathGauge.Mapping

/-- The uncountable discrete set with one cocountable-neighborhood point. -/
abbrev Fortissimo (D : Type u) := Option D

instance (D : Type u) : TopologicalSpace (Fortissimo D) where
  IsOpen s := none ∈ s → {d : D | some d ∉ s}.Countable
  isOpen_univ := by simp
  isOpen_inter := by
    intro s t hs ht h
    have heq : {d : D | some d ∉ s ∩ t} =
        {d : D | some d ∉ s} ∪ {d : D | some d ∉ t} := by
      classical
      ext d
      simp only [mem_setOf_eq, mem_inter_iff, mem_union, not_and_or]
    rw [heq]
    exact (hs h.1).union (ht h.2)
  isOpen_sUnion := by
    intro ss hs h
    obtain ⟨s,hss,hns⟩ := h
    apply (hs s hss hns).mono
    intro d hd hds
    exact hd ⟨s,hss,hds⟩

theorem fortissimo_isOpen {D : Type u} (s : Set (Fortissimo D)) :
    IsOpen s ↔ (none ∈ s → {d : D | some d ∉ s}.Countable) := Iff.rfl

theorem fortissimo_open_some {D : Type u} (d : D) :
    IsOpen ({some d} : Set (Fortissimo D)) := by
  intro h
  cases h

theorem fortissimo_open_compl_some {D : Type u} (d : D) :
    IsOpen ({some d}ᶜ : Set (Fortissimo D)) := by
  intro _
  simpa using (Set.countable_singleton d)

instance (D : Type u) : T2Space (Fortissimo D) where
  t2 := by
    intro x y hxy
    cases x with
    | none =>
      cases y with
      | none => exact (hxy rfl).elim
      | some d =>
        exact ⟨{some d}ᶜ, {some d}, fortissimo_open_compl_some d,
          fortissimo_open_some d, by simp, by simp, disjoint_compl_left⟩
    | some d =>
      refine ⟨{some d}, {some d}ᶜ, fortissimo_open_some d,
        fortissimo_open_compl_some d, by simp, ?_, disjoint_compl_right⟩
      simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hxy.symm

theorem fortissimo_not_open_infty (D : Type u) [Uncountable D] :
    ¬ IsOpen ({none} : Set (Fortissimo D)) := by
  intro h
  have hc := h (by simp)
  have : (univ : Set D).Countable := by simpa using hc
  exact Set.not_countable_univ this

theorem fortissimo_not_discrete (D : Type u) [Uncountable D] :
    ¬ DiscreteTopology (Fortissimo D) := by
  intro h
  exact fortissimo_not_open_infty D (isOpen_discrete _)

theorem fortissimo_countable_closed {D : Type u} {C : Set D} (hC : C.Countable) :
    IsClosed ((some '' C) : Set (Fortissimo D)) := by
  apply isOpen_compl_iff.mp
  intro _
  simpa using hC

theorem fortissimo_some_discrete {D : Type u} (C : Set D) :
    IsDiscrete ((some '' C) : Set (Fortissimo D)) := by
  apply isDiscrete_iff_forall_exists_isOpen.mpr
  intro x hx
  obtain ⟨d,hd,rfl⟩ := hx
  exact ⟨{some d}, fortissimo_open_some d, Set.singleton_inter_of_mem ⟨d,hd,rfl⟩⟩

/-- Every compact subset is finite, without assuming a bound on the underlying set. -/
theorem fortissimo_compact_finite {D : Type u} {K : Set (Fortissimo D)} (hK : IsCompact K) :
    K.Finite := by
  by_contra hi
  have hD : (some ⁻¹' K : Set D).Infinite := by
    intro hf
    have hsub : K ⊆ insert none (some '' (some ⁻¹' K : Set D)) := by
      intro x hx
      cases x with
      | none => simp
      | some d => exact Set.mem_insert_of_mem _ ⟨d,hx,rfl⟩
    exact hi ((hf.image some).insert none |>.subset hsub)
  obtain ⟨C,hCK,hCc,hCi⟩ := hD.exists_subset_countable_infinite
  have hc : IsCompact (some '' C : Set (Fortissimo D)) :=
    hK.of_isClosed_subset (fortissimo_countable_closed hCc) (by
      rintro _ ⟨d,hd,rfl⟩
      exact hCK hd)
  have hf := hc.finite (fortissimo_some_discrete C)
  exact hCi ((Set.finite_image_iff (fun _ _ _ _ h => Option.some.inj h)).mp hf)

instance (D : Type u) : DiscreteTopology (Kify (Fortissimo D)) := by
  apply discreteTopology_iff_isOpen_singleton.mpr
  intro x
  change IsOpen[TopologicalSpace.compactlyGenerated.{u} (Fortissimo D)] {x}
  rw [TopologicalSpace.compactlyGenerated, isOpen_coinduced, isOpen_sigma_iff]
  rintro ⟨S,f⟩
  have hf : (Set.range f).Finite := fortissimo_compact_finite (isCompact_range f.continuous)
  letI : Finite (Set.range f) := hf.to_subtype
  let fc : S → Set.range f := fun s => ⟨f s,⟨s,rfl⟩⟩
  have hfc : Continuous fc := f.continuous.subtype_mk (fun s => ⟨s,rfl⟩)
  have ho : IsOpen {a : Set.range f | a.val = x} := isOpen_discrete _
  exact ho.preimage hfc

/-- The underlying identity is not an original-topology continuous map. -/
theorem fortissimo_not_continuous_to_kify (D : Type u) [Uncountable D] :
    ¬ Continuous (kup : Fortissimo D → Kify (Fortissimo D)) := by
  intro h
  have ho : IsOpen ({kup none} : Set (Kify (Fortissimo D))) := isOpen_discrete _
  exact fortissimo_not_open_infty D (ho.preimage h)

/-- Every probe remains continuous into the kified topology, naturally. -/
def probe_kify_iso (X : Type u) [TopologicalSpace X] : probe X ≅ probe (Kify X) where
  hom.app S f := ⟨fun s => kup (f s), continuous_kprobe (CompHaus.of S.unop) f⟩
  inv.app S f := ⟨fun s => kdown (f s), (continuous_kdown X).comp f.continuous⟩
  hom.naturality := by intros; rfl
  inv.naturality := by intros; rfl

/-- A concrete extra natural transformation absent from `C(X,kX)`. -/
theorem fortissimo_extra_probe_map (D : Type u) [Uncountable D] :
    ∃ η : probe (Fortissimo D) ⟶ probe (Kify (Fortissimo D)),
      ∀ f : C(Fortissimo D,Kify (Fortissimo D)), η ≠ probe_post f := by
  refine ⟨(probe_kify_iso (Fortissimo D)).hom, ?_⟩
  intro f he
  have hf : (f : Fortissimo D → Kify (Fortissimo D)) = kup := by
    funext x
    have hp := congrArg (fun η => probe_point η x) he
    exact hp.symm
  apply fortissimo_not_continuous_to_kify D
  exact hf ▸ f.continuous

theorem powerset_nat_uncountable : Uncountable (Set ℕ) := by
  rw [← not_countable_iff]
  intro h
  letI := h
  obtain ⟨f,hf⟩ := exists_injective_nat (Set ℕ)
  exact Function.cantor_injective f hf

/-- The precise example suggested in the reference, with no uninstantiated cardinality premise. -/
theorem powerset_nat_extra_probe_map :
    ∃ η : probe (Fortissimo (Set ℕ)) ⟶ probe (Kify (Fortissimo (Set ℕ))),
      ∀ f : C(Fortissimo (Set ℕ),Kify (Fortissimo (Set ℕ))), η ≠ probe_post f := by
  letI := powerset_nat_uncountable
  exact fortissimo_extra_probe_map (Set ℕ)

end MathGauge.Mapping
