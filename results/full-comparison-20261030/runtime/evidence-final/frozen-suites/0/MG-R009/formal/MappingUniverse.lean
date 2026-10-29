import MappingNaturality

noncomputable section
open TopologicalSpace Topology Set CategoryTheory Opposite
universe u v w
namespace MathGauge.Mapping

/-- Canonical universe enlargement of a set-valued presheaf, not a restriction of its maps. -/
abbrev lift_presheaf {C : Type w} [Category C] (F : C ⥤ Type u) : C ⥤ Type (max u v) where
  obj X := ULift.{v} (F.obj X)
  map f x := ⟨F.map f x.down⟩
  map_id X := by funext x; cases x; simp
  map_comp f g := by funext x; cases x; simp

/-- Every natural transformation of the enlarged presheaves descends uniquely. -/
def lift_nat_equiv {C : Type w} [Category C] (F G : C ⥤ Type u) :
    (F ⟶ G) ≃ (lift_presheaf.{u,v} F ⟶ lift_presheaf.{u,v} G) where
  toFun η := {
    app X x := ⟨η.app X x.down⟩
    naturality := by
      intro X Y f
      funext x
      apply ULift.ext
      exact ConcreteCategory.congr_hom (η.naturality f) x.down }
  invFun η := {
    app X x := (η.app X ⟨x⟩).down
    naturality := by
      intro X Y f
      funext x
      exact congrArg ULift.down (ConcreteCategory.congr_hom (η.naturality f) ⟨x⟩) }
  left_inv η := by ext X x; rfl
  right_inv η := by ext X x; rfl

abbrev probeV (X : Type u) [TopologicalSpace X] : Profinite.{u}ᵒᵖ ⥤ Type (max u v) :=
  lift_presheaf.{u,v} (probe X)

abbrev probe_productV (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    Profinite.{u}ᵒᵖ ⥤ Type (max u v) where
  obj S := (probeV.{u,v} X).obj S × (probeV.{u,v} Y).obj S
  map a p := ((probeV.{u,v} X).map a p.1, (probeV.{u,v} Y).map a p.2)

def lift_product_iso (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    lift_presheaf.{u,v} (probe_product X Y) ≅ probe_productV.{u,v} X Y where
  hom.app S p := (⟨p.down.1⟩,⟨p.down.2⟩)
  inv.app S p := ⟨p.1.down,p.2.down⟩

def lift_product_nat_equiv (X Y Z : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] :
    (probe_product X Y ⟶ probe Z) ≃ (probe_productV.{u,v} X Y ⟶ probeV.{u,v} Z) :=
  (lift_nat_equiv _ _).trans {
    toFun η := (lift_product_iso X Y).inv ≫ η
    invFun η := (lift_product_iso X Y).hom ≫ η
    left_inv η := by simp
    right_inv η := by simp }

/-- The larger ambient set universe in the task yields exactly the same mapping records. -/
def realization_equivV (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (S : Profinite.{u}) :
    C(S,Realization X Y) ≃ (probe_productV.{u,v} S X ⟶ probeV.{u,v} Y) :=
  (realization_equiv S).trans (lift_product_nat_equiv S X Y)

def all_parameter_equivV (X Y Z : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [T2Space X] :
    (probeV.{u,v} Z ⟶ probeV.{u,v} (Realization X Y)) ≃
      (probe_productV.{u,v} Z X ⟶ probeV.{u,v} Y) :=
  (lift_nat_equiv _ _).symm.trans
    (all_parameter_equiv.trans (lift_product_nat_equiv Z X Y))

def probe_product_leftV {X Z W : Type u} [TopologicalSpace X] [TopologicalSpace Z]
    [TopologicalSpace W] (α : probeV.{u,v} Z ⟶ probeV.{u,v} W) :
    probe_productV.{u,v} Z X ⟶ probe_productV.{u,v} W X where
  app S p := (α.app S p.1,p.2)
  naturality := by
    intro S T a
    funext p
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (α.naturality a) p.1
    · rfl

def evaluationV (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] :
    probe_productV.{u,v} (Realization X Y) X ⟶ probeV.{u,v} Y :=
  lift_product_nat_equiv _ _ _ evaluation

theorem evaluationV_induces_equiv (X Y Z : Type u) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [T2Space X]
    (α : probeV.{u,v} Z ⟶ probeV.{u,v} (Realization X Y)) :
    all_parameter_equivV X Y Z α = probe_product_leftV α ≫ evaluationV X Y := by
  let β : probe Z ⟶ probe (Realization X Y) := (lift_nat_equiv _ _).symm α
  exact congrArg (lift_product_nat_equiv Z X Y) (evaluation_induces_equiv β)

theorem evaluationV_bijective (X Y Z : Type u) [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace Z] [T2Space X] :
    Function.Bijective (fun α : probeV.{u,v} Z ⟶ probeV.{u,v} (Realization X Y) =>
      probe_product_leftV α ≫ evaluationV X Y) := by
  have h : (fun α : probeV.{u,v} Z ⟶ probeV.{u,v} (Realization X Y) =>
      probe_product_leftV α ≫ evaluationV X Y) = all_parameter_equivV X Y Z := by
    funext α
    exact (evaluationV_induces_equiv X Y Z α).symm
  rw [h]
  exact (all_parameter_equivV X Y Z).bijective

/-- The record presheaf with the restriction operation stated in MG-R010. -/
abbrev mapping_recordsV (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    Profinite.{u}ᵒᵖ ⥤ Type (max (u+1) v) where
  obj S := probe_productV.{u,v} S.unop X ⟶ probeV.{u,v} Y
  map a η := probe_product_leftV
    ((lift_nat_equiv _ _) (probe_post a.unop.hom.hom)) ≫ η
  map_id S := by ext η T p; rfl
  map_comp a b := by ext η T p; rfl

/-- Representation is a natural isomorphism of presheaves, in the ambient universe. -/
def realization_isoV (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space X] :
    probeV.{u,max (u+1) v} (Realization X Y) ≅ mapping_recordsV.{u,max (u+1) v} X Y := by
  exact NatIso.ofComponents (fun S => (Equiv.trans Equiv.ulift
    (realization_equivV.{u,max (u+1) v} X Y S.unop)).toIso)

theorem realization_hausdorff (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] : T2Space (Realization X Y) := inferInstance

theorem realization_small (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    Small.{u} (Realization X Y) := inferInstance

theorem records_small (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] [T2Space X]
    (S : Profinite.{u}) :
    Small.{u} (probe_productV.{u,v} S X ⟶ probeV.{u,v} Y) :=
  small_of_injective (realization_equivV.{u,v} X Y S).symm.injective

@[reducible] def realization_empty_source (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    [IsEmpty X] : Unique (Realization X Y) := by
  letI : IsEmpty (Kify X) := ⟨fun x => isEmptyElim (kdown x)⟩
  refine ⟨⟨fun x => isEmptyElim x, continuous_of_discreteTopology⟩, ?_⟩
  intro f
  apply ContinuousMap.ext
  intro x
  exact isEmptyElim x

theorem realization_empty_target (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y]
    [Nonempty X] [IsEmpty Y] : IsEmpty (Realization X Y) := by
  refine ⟨fun f => ?_⟩
  obtain ⟨x⟩ := ‹Nonempty X›
  exact isEmptyElim (kdown (kdown f (kup x)))

end MathGauge.Mapping
