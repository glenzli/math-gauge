import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Tactic

noncomputable section
open Set Filter Function Topology
namespace MathGauge.UltrafilterAlgebras
universe u v w


/-- Exact membership formula for the multiplication used in the task. -/
theorem mem_join {X : Type u} (W : Ultrafilter (Ultrafilter X)) (S : Set X) :
    S ∈ joinM W ↔ {U : Ultrafilter X | S ∈ U} ∈ W := Iff.rfl

/-- Exact membership formula for pushforward. -/
theorem mem_pushforward {X : Type u} {Y : Type v} (f : X → Y)
    (U : Ultrafilter X) (S : Set Y) : S ∈ U.map f ↔ f ⁻¹' S ∈ U := Iff.rfl

/-- The input consists of the two algebra equations, with no topology on X. -/
structure Algebra (X : Type u) where
  limit : Ultrafilter X → X
  unit : ∀ x, limit (pure x) = x
  assoc : ∀ W : Ultrafilter (Ultrafilter X), limit (joinM W) = limit (W.map limit)


@[ext] theorem Algebra.ext {X : Type u} {a b : Algebra X} (h : a.limit = b.limit) : a = b := by
  cases a
  cases b
  cases h
  rfl

/-- Closed kernel theorem proved solely in the existing Stone topology on Ultrafilter X. -/
theorem kernel_closed {X : Type u} (a : Algebra X) :
    IsClosed {p : Ultrafilter X × Ultrafilter X | a.limit p.1 = a.limit p.2} := by
  rw [isClosed_iff_ultrafilter]
  intro p W hW hR
  have hfst : ((W.map Prod.fst : Ultrafilter (Ultrafilter X)) : Filter (Ultrafilter X)) ≤ 𝓝 p.1 :=
    (continuous_fst.tendsto p).comp hW
  have hsnd : ((W.map Prod.snd : Ultrafilter (Ultrafilter X)) : Filter (Ultrafilter X)) ≤ 𝓝 p.2 :=
    (continuous_snd.tendsto p).comp hW
  have heq : (W.map Prod.fst).map a.limit = (W.map Prod.snd).map a.limit := by
    apply Ultrafilter.coe_injective
    simp only [Ultrafilter.coe_map, Filter.map_map]
    exact Filter.map_congr hR
  change a.limit p.1 = a.limit p.2
  rw [ultrafilter_converges_iff.mp hfst, ultrafilter_converges_iff.mp hsnd,
    a.assoc, a.assoc, heq]

/-- General compact Hausdorff closed-kernel quotient construction. -/
theorem compact_quotient_t2 {K : Type u} {X : Type v} [TopologicalSpace K]
    [CompactSpace K] [T2Space K] (q : K → X) (hq : Surjective q)
    (hR : IsClosed {p : K × K | q p.1 = q p.2}) :
    @T2Space X (TopologicalSpace.coinduced q inferInstance) := by
  letI : TopologicalSpace X := TopologicalSpace.coinduced q inferInstance
  have qc : Continuous q := continuous_coinduced_rng
  have qclosed : IsClosedMap q := by
    intro F hF
    rw [isClosed_coinduced]
    have hsat : q ⁻¹' (q '' F) = Prod.snd '' ((F ×ˢ univ) ∩ {p : K × K | q p.1 = q p.2}) := by
      ext z
      simp only [mem_preimage, mem_image, mem_inter_iff, mem_prod, mem_univ,
        and_true, mem_setOf_eq]
      constructor
      · rintro ⟨y,hy,heq⟩; exact ⟨(y,z),⟨hy,heq⟩,rfl⟩
      · rintro ⟨⟨y,z'⟩,⟨hy,heq⟩,rfl⟩; exact ⟨y,hy,heq⟩
    rw [hsat]
    exact (((hF.prod isClosed_univ).inter hR).isCompact.image continuous_snd).isClosed
  have hfibre (x : X) : IsClosed (q ⁻¹' {x}) := by
    obtain ⟨k,rfl⟩ := hq x
    exact hR.preimage (continuous_id.prodMk continuous_const)
  constructor
  intro x y hxy
  have hdisj : Disjoint (q ⁻¹' {x}) (q ⁻¹' {y}) := by
    rw [disjoint_left]
    intro k hkx hky
    exact hxy (hkx.symm.trans hky)
  obtain ⟨U,V,hU,hV,hxU,hyV,hUV⟩ :=
    SeparatedNhds.of_isCompact_isCompact (hfibre x).isCompact (hfibre y).isCompact hdisj
  let U' := (q '' Uᶜ)ᶜ
  let V' := (q '' Vᶜ)ᶜ
  refine ⟨U',V',(qclosed Uᶜ hU.isClosed_compl).isOpen_compl,
    (qclosed Vᶜ hV.isClosed_compl).isOpen_compl,?_,?_,?_⟩
  · rintro ⟨k,hk,hkx⟩
    exact hk (hxU hkx)
  · rintro ⟨k,hk,hky⟩
    exact hk (hyV hky)
  · rw [disjoint_left]
    intro z hzU hzV
    obtain ⟨k,rfl⟩ := hq z
    have hkU : k ∈ U := by by_contra h; exact hzU ⟨k,h,rfl⟩
    have hkV : k ∈ V := by by_contra h; exact hzV ⟨k,h,rfl⟩
    exact disjoint_left.mp hUV hkU hkV

/-- The constructed topology is final for the algebra operation from the Stone space. -/
@[reducible] def Algebra.topology {X : Type u} (a : Algebra X) : TopologicalSpace X :=
  TopologicalSpace.coinduced a.limit inferInstance

theorem limit_surjective {X : Type u} (a : Algebra X) : Surjective a.limit :=
  fun x => ⟨pure x,a.unit x⟩

theorem constructed_t2 {X : Type u} (a : Algebra X) : @T2Space X a.topology :=
  compact_quotient_t2 a.limit (limit_surjective a) (kernel_closed a)

theorem constructed_compact {X : Type u} (a : Algebra X) : @CompactSpace X a.topology := by
  letI := a.topology
  have h : IsCompact (range a.limit) := isCompact_range continuous_coinduced_rng
  rw [range_eq_univ.mpr (limit_surjective a)] at h
  exact isCompact_univ_iff.mp h

theorem limit_continuous {X : Type u} (a : Algebra X) :
    @Continuous (Ultrafilter X) X inferInstance a.topology a.limit := continuous_coinduced_rng

/-- In the constructed topology, each ultrafilter has exactly the specified limit. -/
theorem converges_iff {X : Type u} (a : Algebra X) (U : Ultrafilter X) (x : X) :
    @LE.le (Filter X) _ U (@nhds X a.topology x) ↔ a.limit U = x := by
  letI := a.topology
  letI : T2Space X := constructed_t2 a
  letI : CompactSpace X := constructed_compact a
  have heq : a.limit = Ultrafilter.extend (id : X → X) := by
    apply denseRange_pure.equalizer (limit_continuous a) (continuous_ultrafilter_extend id)
    funext x
    simp only [comp_apply, ultrafilter_extend_pure, id_eq, a.unit]
  rw [heq, ultrafilter_extend_eq_iff]
  simp

/-- Any topology having the specified ultrafilter limits must be the constructed topology. -/
theorem topology_unique {X : Type u} (a : Algebra X) (t : TopologicalSpace X)
    (hlim : ∀ (U : Ultrafilter X) (x : X), @LE.le (Filter X) _ U (@nhds X t x) ↔ a.limit U = x) :
    t = a.topology := by
  apply TopologicalSpace.ext_isClosed
  intro s
  rw [@isClosed_iff_ultrafilter X s t, @isClosed_iff_ultrafilter X s a.topology]
  simp only [hlim, converges_iff]

/-- A homomorphism of the given algebra operations. -/
def Hom {X : Type u} {Y : Type v} (a : Algebra X) (b : Algebra Y) (f : X → Y) : Prop :=
  ∀ U : Ultrafilter X, f (a.limit U) = b.limit (U.map f)


/-- The identity is the same underlying function on both sides of the correspondence. -/
theorem hom_id {X : Type u} (a : Algebra X) : Hom a a id := by
  intro U
  simp

/-- Composition is the same underlying function on both sides of the correspondence. -/
theorem hom_comp {X : Type u} {Y : Type v} {Z : Type w}
    (a : Algebra X) (b : Algebra Y) (c : Algebra Z) (f : X → Y) (g : Y → Z)
    (hf : Hom a b f) (hg : Hom b c g) : Hom a c (g ∘ f) := by
  intro U
  change g (f (a.limit U)) = c.limit (U.map (g ∘ f))
  rw [hf U, hg (U.map f), Ultrafilter.map_map]

/-- The correspondence also identifies all morphisms, without adding continuity as input. -/
theorem hom_iff_continuous {X : Type u} {Y : Type v} (a : Algebra X) (b : Algebra Y) (f : X → Y) :
    Hom a b f ↔ @Continuous X Y a.topology b.topology f := by
  letI := a.topology
  letI := b.topology
  rw [continuous_iff_ultrafilter]
  constructor
  · intro h x U hU
    apply (converges_iff b (U.map f) (f x)).mpr
    rw [← h U, (converges_iff a U x).mp hU]
  · intro h U
    exact ((converges_iff b (U.map f) (f (a.limit U))).mp
      (h (a.limit U) U ((converges_iff a U _).mpr rfl))).symm

section Converse
variable {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]

def usualLimit : Ultrafilter X → X := Ultrafilter.extend id

theorem usualLimit_converges (U : Ultrafilter X) : (U : Filter X) ≤ 𝓝 (usualLimit U) := by
  simpa [usualLimit] using (ultrafilter_extend_eq_iff (f := id) (b := U)).mp rfl

def fromTopology : Algebra X where
  limit := usualLimit
  unit x := ultrafilter_extend_pure id x
  assoc W := by
    have hW : (W : Filter (Ultrafilter X)) ≤ 𝓝 (joinM W) := ultrafilter_converges_iff.mpr rfl
    have h1 : ((W.map usualLimit : Ultrafilter X) : Filter X) ≤ 𝓝 (usualLimit (joinM W)) :=
      (continuous_ultrafilter_extend id).tendsto _ |>.comp hW
    exact tendsto_nhds_unique h1 (usualLimit_converges (W.map usualLimit))

theorem topology_roundtrip : (fromTopology (X := X)).topology = (inferInstance : TopologicalSpace X) := by
  symm
  apply topology_unique
  intro U x
  change (U : Filter X) ≤ 𝓝 x ↔ usualLimit U = x
  simpa [usualLimit] using (ultrafilter_extend_eq_iff (f := id) (b := U) (c := x)).symm

end Converse


/-- Reconstructing the topology and then its limit operation returns the original algebra. -/
theorem algebra_roundtrip {X : Type u} (a : Algebra X) :
    @fromTopology X a.topology (constructed_compact a) (constructed_t2 a) = a := by
  letI := a.topology
  letI : CompactSpace X := constructed_compact a
  letI : T2Space X := constructed_t2 a
  apply Algebra.ext
  funext U
  exact ((converges_iff a U (usualLimit U)).mp (usualLimit_converges U)).symm

/-- Exact existence-and-uniqueness endpoint, including compactness and Hausdorffness. -/
theorem main {X : Type u} (a : Algebra X) : ∃! t : TopologicalSpace X,
    @CompactSpace X t ∧ @T2Space X t ∧
    ∀ (U : Ultrafilter X) (x : X), @LE.le (Filter X) _ U (@nhds X t x) ↔ a.limit U = x := by
  refine ⟨a.topology, ⟨constructed_compact a,constructed_t2 a,converges_iff a⟩,?_⟩
  intro t ht
  exact topology_unique a t ht.2.2

end MathGauge.UltrafilterAlgebras
