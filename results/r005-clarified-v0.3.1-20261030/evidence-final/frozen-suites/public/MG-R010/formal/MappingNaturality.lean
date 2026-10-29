import MappingRecords

noncomputable section
open TopologicalSpace Topology Set CategoryTheory Opposite
universe u
namespace MathGauge.Mapping

variable {X X' X'' Y Y' Y'' Z Z' : Type u}
  [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace X'']
  [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Y'']
  [TopologicalSpace Z] [TopologicalSpace Z']

def probe_post (f : C(X,Y)) : probe X ⟶ probe Y where
  app S g := f.comp g
  naturality := by intros; rfl

def probe_product_map_right (β : probe X' ⟶ probe X) :
    probe_product Z X' ⟶ probe_product Z X where
  app S p := (p.1,β.app S p.2)
  naturality := by
    intro S T a
    funext p
    apply Prod.ext
    · rfl
    · exact ConcreteCategory.congr_hom (β.naturality a) p.2

theorem probe_product_map_left_comp {W : Type u} [TopologicalSpace W]
    (α : probe Z' ⟶ probe Z) (β : probe Z ⟶ probe W) :
    probe_product_map_left (X := X) (α ≫ β) =
      probe_product_map_left α ≫ probe_product_map_left β := rfl

theorem all_parameter_natural [T2Space X]
    (β : probe Z' ⟶ probe Z) (α : probe Z ⟶ probe (Realization X Y)) :
    all_parameter_equiv (β ≫ α) = probe_product_map_left β ≫ all_parameter_equiv α := by
  simp only [evaluation_induces_equiv, probe_product_map_left_comp, Category.assoc]

theorem realization_natural [T2Space X] (S S' : Profinite.{u})
    (v : C(S',S)) (f : C(S,Realization X Y)) :
    realization_equiv S' (f.comp v) =
      probe_product_map_left (probe_post v) ≫ realization_equiv S f := by
  ext T p t
  rfl

/-- Pre- and postcomposition on the actual compact-open carriers are continuous. -/
def realization_map (a : C(X',X)) (b : C(Y,Y')) : C(Realization X Y,Realization X' Y') :=
  kmap ⟨fun f : C(Kify X,Kify Y) => (kmap b).comp (f.comp (kmap a)),
    (ContinuousMap.continuous_postcomp (kmap b)).comp
      (ContinuousMap.continuous_precomp (kmap a))⟩

@[simp] theorem realization_map_apply (a : C(X',X)) (b : C(Y,Y'))
    (f : Realization X Y) (x : Kify X') :
    kdown (realization_map a b f) x = (kmap b) (kdown f ((kmap a) x)) := rfl

@[simp] theorem realization_map_id :
    realization_map (ContinuousMap.id X) (ContinuousMap.id Y) =
      ContinuousMap.id (Realization X Y) := by ext f; rfl

@[simp] theorem realization_map_comp (a : C(X',X)) (a' : C(X'',X'))
    (b : C(Y,Y')) (b' : C(Y',Y'')) :
    realization_map (a.comp a') (b'.comp b) =
      (realization_map a' b').comp (realization_map a b) := by ext f; rfl

theorem family_record_natural_XY [T2Space X] [T2Space X']
    (a : C(X',X)) (b : C(Y,Y')) (f : C(Kify Z,Realization X Y)) :
    family_record_equiv ((realization_map a b).comp f) =
      probe_product_map_right (probe_post a) ≫ family_record_equiv f ≫ probe_post b := by
  ext S p s
  rfl

theorem realization_natural_XY [T2Space X] [T2Space X']
    (a : C(X',X)) (b : C(Y,Y')) (S : Profinite.{u}) (f : C(S,Realization X Y)) :
    realization_equiv S ((realization_map a b).comp f) =
      probe_product_map_right (probe_post a) ≫ realization_equiv S f ≫ probe_post b := by
  ext T p t
  rfl

theorem all_parameter_natural_XY [T2Space X] [T2Space X']
    (a : C(X',X)) (b : C(Y,Y')) (α : probe Z ⟶ probe (Realization X Y)) :
    all_parameter_equiv (α ≫ probe_post (realization_map a b)) =
      probe_product_map_right (probe_post a) ≫ all_parameter_equiv α ≫ probe_post b := by
  ext S p s
  rfl

/-- Probe isomorphisms determine a homeomorphism after kification. -/
def probe_iso_homeo (e : probe X ≅ probe Y) : Kify X ≃ₜ Kify Y where
  toFun := probe_to_map e.hom
  invFun := probe_to_map e.inv
  left_inv x := by
    have h : (probe_to_map e.inv).comp (probe_to_map e.hom) = ContinuousMap.id (Kify X) := by
      apply probe_map_equiv.symm.injective
      change map_to_probe ((probe_to_map e.inv).comp (probe_to_map e.hom)) =
        map_to_probe (ContinuousMap.id (Kify X))
      rw [map_to_probe_comp, map_to_probe_id]
      have h₁ := probe_map_equiv.left_inv e.hom
      have h₂ := probe_map_equiv.left_inv e.inv
      change map_to_probe (probe_to_map e.hom) = e.hom at h₁
      change map_to_probe (probe_to_map e.inv) = e.inv at h₂
      rw [h₁,h₂]
      exact e.hom_inv_id
    exact congrArg (fun f : C(Kify X,Kify X) => f x) h
  right_inv y := by
    have h : (probe_to_map e.hom).comp (probe_to_map e.inv) = ContinuousMap.id (Kify Y) := by
      apply probe_map_equiv.symm.injective
      change map_to_probe ((probe_to_map e.hom).comp (probe_to_map e.inv)) =
        map_to_probe (ContinuousMap.id (Kify Y))
      rw [map_to_probe_comp, map_to_probe_id]
      have h₁ := probe_map_equiv.left_inv e.hom
      have h₂ := probe_map_equiv.left_inv e.inv
      change map_to_probe (probe_to_map e.hom) = e.hom at h₁
      change map_to_probe (probe_to_map e.inv) = e.inv at h₂
      rw [h₁,h₂]
      exact e.inv_hom_id
    exact congrArg (fun f : C(Kify Y,Kify Y) => f y) h
  continuous_toFun := (probe_to_map e.hom).continuous
  continuous_invFun := (probe_to_map e.inv).continuous

/-- The correct uniqueness conclusion for an arbitrary Hausdorff realization. -/
def realization_unique_after_kify (e : probe Z ≅ probe (Realization X Y)) :
    Kify Z ≃ₜ Realization X Y :=
  (probe_iso_homeo e).trans (kify_homeo (Realization X Y))

end MathGauge.Mapping
