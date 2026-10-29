import ObservationTopology

noncomputable section
open Set Filter Function Topology
namespace MathGauge.ProductAlgebras
open MathGauge.UltrafilterAlgebras MathGauge.ObservationTopology
universe u v w

/-- Naturality of multiplication proved directly from the set-membership rule. -/
theorem map_join {X : Type u} {Y : Type v} (f : X → Y)
    (W : Ultrafilter (Ultrafilter X)) : (joinM W).map f=joinM (W.map (Ultrafilter.map f)) := by
  ext S
  rfl

/-- Coordinate pushforwards are taken from the actual ultrafilter on X×Y;
no identification U(X×Y)=U(X)×U(Y) is made. -/
def product {X : Type u} {Y : Type v} (a : Algebra X) (b : Algebra Y) : Algebra (X × Y) where
  limit U := (a.limit (U.map Prod.fst),b.limit (U.map Prod.snd))
  unit x := by simp [Ultrafilter.map_pure,a.unit,b.unit]
  assoc W := by
    apply Prod.ext
    · change a.limit ((joinM W).map Prod.fst)=
        a.limit ((W.map (fun U => (a.limit (U.map Prod.fst),b.limit (U.map Prod.snd)))).map Prod.fst)
      rw [map_join,a.assoc,Ultrafilter.map_map,Ultrafilter.map_map]
      rfl
    · change b.limit ((joinM W).map Prod.snd)=
        b.limit ((W.map (fun U => (a.limit (U.map Prod.fst),b.limit (U.map Prod.snd)))).map Prod.snd)
      rw [map_join,b.assoc,Ultrafilter.map_map,Ultrafilter.map_map]
      rfl

theorem product_topology {X : Type u} {Y : Type v} (a : Algebra X) (b : Algebra Y) :
    letI := a.topology
    letI := b.topology
    (product a b).topology=(inferInstance : TopologicalSpace (X × Y)) := by
  letI := a.topology
  letI := b.topology
  symm
  apply topology_unique
  intro U x
  rw [nhds_prod_eq,Filter.le_prod]
  change (((U.map Prod.fst : Ultrafilter X) : Filter X) ≤ 𝓝 x.1 ∧
    ((U.map Prod.snd : Ultrafilter Y) : Filter Y) ≤ 𝓝 x.2) ↔
    (a.limit (U.map Prod.fst),b.limit (U.map Prod.snd))=x
  rw [converges_iff a,converges_iff b]
  constructor
  · rintro ⟨h₁,h₂⟩
    exact Prod.ext h₁ h₂
  · intro h
    exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩

/-- The finite-observation quotient for this algebra's recovered topology is
the ordinary product quotient, by the proved topology equality. -/
def productObservationHomeomorph {X : Type u} {Y : Type v} (a : Algebra X) (b : Algebra Y) :
    letI := a.topology
    letI := b.topology
    ObservationImage (X × Y) ≃ₜ ObservationImage X × ObservationImage Y := by
  letI := a.topology
  letI := b.topology
  letI : CompactSpace X := constructed_compact a
  letI : CompactSpace Y := constructed_compact b
  letI : T2Space X := constructed_t2 a
  letI : T2Space Y := constructed_t2 b
  exact observationProductHomeomorph X Y

end MathGauge.ProductAlgebras
