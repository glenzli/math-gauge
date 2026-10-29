import ProbeNaturality

noncomputable section
open TopologicalSpace Topology Set CategoryTheory Opposite
universe u
namespace MathGauge.Mapping

variable {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The pointwise product specified in the question. -/
abbrev probe_product (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    Profinite.{u}ᵒᵖ ⥤ Type u where
  obj S := C(S.unop,X) × C(S.unop,Y)
  map a fg := (fg.1.comp a.unop.hom.hom, fg.2.comp a.unop.hom.hom)

def probe_product_iso (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    probe (X × Y) ≅ probe_product X Y where
  hom.app S f := (ContinuousMap.fst.comp f, ContinuousMap.snd.comp f)
  inv.app S fg := fg.1.prodMk fg.2
  hom_inv_id := by ext S f s <;> rfl
  inv_hom_id := by ext S f <;> rfl

def product_nat_equiv : (probe_product Z X ⟶ probe Y) ≃ (probe (Z × X) ⟶ probe Y) where
  toFun η := (probe_product_iso Z X).hom ≫ η
  invFun η := (probe_product_iso Z X).inv ≫ η
  left_inv η := by simp
  right_inv η := by simp

def product_map_equiv : C(Kify (Z × X),Kify Y) ≃ C(kprod (Kify Z) (Kify X),Kify Y) where
  toFun f := f.comp ⟨(kify_product_homeo Z X).symm, (kify_product_homeo Z X).symm.continuous⟩
  invFun f := f.comp ⟨kify_product_homeo Z X, (kify_product_homeo Z X).continuous⟩
  left_inv f := by ext p; rfl
  right_inv f := by ext p; rfl

def product_probe_map_equiv :
    (probe_product Z X ⟶ probe Y) ≃ C(kprod (Kify Z) (Kify X),Kify Y) :=
  product_nat_equiv.trans (probe_map_equiv.trans product_map_equiv)

/-- The requested underlying set is `C(kX,kY)`; the topology is kified compact-open. -/
abbrev Realization (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :=
  KMap (Kify X) (Kify Y)

def family_record_equiv [T2Space X] :
    C(Kify Z,Realization X Y) ≃ (probe_product Z X ⟶ probe Y) :=
  exponential_equiv.trans product_probe_map_equiv.symm

@[simp] theorem family_record_apply [T2Space X]
    (f : C(Kify Z,Realization X Y)) (S : Profinite.{u})
    (p : C(S,Z) × C(S,X)) (s : S) :
    (family_record_equiv f).app (op S) p s = kdown (kdown (f (kup (p.1 s))) (kup (p.2 s))) := rfl

def cg_target_map_equiv {W V : Type u} [TopologicalSpace W] [TopologicalSpace V]
    [UCompactlyGeneratedSpace.{u} V] : C(Kify W,Kify V) ≃ C(Kify W,V) where
  toFun f := (⟨kify_homeo V, (kify_homeo V).continuous⟩ : C(Kify V,V)).comp f
  invFun f := (⟨(kify_homeo V).symm, (kify_homeo V).symm.continuous⟩ : C(V,Kify V)).comp f
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl

/-- All Hausdorff parameter spaces, including ones not initially compactly generated. -/
def all_parameter_equiv [T2Space X] :
    (probe Z ⟶ probe (Realization X Y)) ≃ (probe_product Z X ⟶ probe Y) :=
  probe_map_equiv.trans (cg_target_map_equiv.trans family_record_equiv)

def probe_source_map_equiv (S : Profinite.{u}) :
    C(S,Realization X Y) ≃ C(Kify S,Realization X Y) where
  toFun f := f.comp ⟨kify_homeo S, (kify_homeo S).continuous⟩
  invFun f := f.comp ⟨(kify_homeo S).symm, (kify_homeo S).symm.continuous⟩
  left_inv f := by ext x; rfl
  right_inv f := by ext x; rfl

/-- Representation on every profinite parameter, not just the point. -/
def realization_equiv [T2Space X] (S : Profinite.{u}) :
    C(S,Realization X Y) ≃ (probe_product S X ⟶ probe Y) :=
  (probe_source_map_equiv S).trans family_record_equiv

def probe_product_map_left {W : Type u} [TopologicalSpace W]
    (α : probe Z ⟶ probe W) : probe_product Z X ⟶ probe_product W X where
  app S p := (α.app S p.1,p.2)
  naturality := by
    intro S T a
    funext p
    apply Prod.ext
    · exact ConcreteCategory.congr_hom (α.naturality a) p.1
    · rfl

/-- The evaluation natural transformation, constructed from the proved exponential law. -/
def evaluation [T2Space X] : probe_product (Realization X Y) X ⟶ probe Y :=
  all_parameter_equiv (𝟙 (probe (Realization X Y)))

@[simp] theorem evaluation_apply [T2Space X] (S : Profinite.{u})
    (p : C(S,Realization X Y) × C(S,X)) (s : S) :
    (evaluation (X := X) (Y := Y)).app (op S) p s =
      kdown (kdown (p.1 s) (kup (p.2 s))) := rfl

/-- The question's evaluation operation is precisely the constructed bijection. -/
theorem evaluation_induces_equiv [T2Space X] (α : probe Z ⟶ probe (Realization X Y)) :
    all_parameter_equiv α = probe_product_map_left α ≫ evaluation := by
  ext S p s
  exact congrArg (fun f : C(S.unop,Realization X Y) => kdown (kdown (f s) (kup (p.2 s))))
    (show ContinuousMap.const S.unop (probe_point α (p.1 s)) =
      ContinuousMap.const S.unop (α.app S p.1 s) from
      congrArg (ContinuousMap.const S.unop) (probe_naturality_point α S.unop p.1 s).symm)

theorem evaluation_bijective [T2Space X] :
    Function.Bijective (fun α : probe Z ⟶ probe (Realization X Y) =>
      probe_product_map_left α ≫ evaluation) := by
  have h : (fun α : probe Z ⟶ probe (Realization X Y) =>
      probe_product_map_left α ≫ evaluation) = all_parameter_equiv := by
    funext α
    exact (evaluation_induces_equiv α).symm
  rw [h]
  exact all_parameter_equiv.bijective

end MathGauge.Mapping
