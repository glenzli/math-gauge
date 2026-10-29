import LinearSystems

noncomputable section
namespace MathGauge.LinearSystems
universe u v w z
variable {k : Type u} [Field k]
variable {E : Type v} [AddCommGroup E] [Module k E]
variable {V : Type w} [AddCommGroup V] [Module k V]
variable {H : Type z} [AddCommGroup H] [Module k H]
variable (T : E →ₗ[k] V) (b : E →ₗ[k] k) (A : H →ₗ[k] V) (g : H →ₗ[k] k)

def restrictionFiber := {f : Solutions T b // f.val.comp A = g}

/-- The augmented equations are exactly the original solutions with prescribed observations. -/
def augmentedEquiv : Solutions (T.coprod A) (b.coprod g) ≃ restrictionFiber T b A g where
  toFun f := ⟨⟨f.val, by
    ext e
    simpa using LinearMap.congr_fun f.property (e,0)⟩, by
      ext h
      simpa using LinearMap.congr_fun f.property (0,h)⟩
  invFun f := ⟨f.val.val, by
    apply LinearMap.ext
    intro x
    change f.val.val (T x.1+A x.2)=b x.1+g x.2
    rw [map_add]
    exact congrArg₂ (· + ·) (LinearMap.congr_fun f.val.property x.1)
      (LinearMap.congr_fun f.property x.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact image criterion: the observation constants agree on every finite row relation. -/
theorem restriction_image : Nonempty (restrictionFiber T b A g) ↔
    ∀ e h, T e=A h → b e=g h := by
  constructor
  · rintro ⟨f⟩ e h he
    exact (LinearMap.congr_fun f.val.property e).symm.trans
      ((congrArg f.val.val he).trans (LinearMap.congr_fun f.property h))
  · intro h
    have hc : LinearMap.ker (T.coprod A) ≤ LinearMap.ker (b.coprod g) := by
      intro x hx
      change T x.1+A x.2=0 at hx
      change b x.1+g x.2=0
      have he : T x.1=A (-x.2) := by rw [map_neg]; exact eq_neg_of_add_eq_zero_left hx
      rw [h _ _ he, map_neg, neg_add_cancel]
    obtain ⟨f⟩ := (solvable_iff _ _).2 hc
    exact ⟨augmentedEquiv T b A g f⟩

/-- Actual parameterization of each nonempty fiber by a quotient dual. -/
def restrictionFiberEquiv (f0 : restrictionFiber T b A g) :
    ((V ⧸ (LinearMap.range T ⊔ LinearMap.range A)) →ₗ[k] k) ≃
      restrictionFiber T b A g := by
  have he : LinearMap.range (T.coprod A)=LinearMap.range T ⊔ LinearMap.range A :=
    LinearMap.range_coprod T A
  rw [← he]
  exact (solutionEquiv _ _ ((augmentedEquiv T b A g).symm f0)).trans
    (augmentedEquiv T b A g)

section Coordinates
variable {I : Type v} {J : Type z}
variable (r : J → I →₀ k) (d : J → k) (S : Set I)

def observationMap : (S →₀ k) →ₗ[k] (I →₀ k) :=
  Finsupp.linearCombination k (fun i : S => Finsupp.single i.val 1)

def coordinateFiber (y : S → k) := {x : coordinateSolutions r d // ∀ i : S, x.val i=y i}

theorem observation_equation (x : I → k) (y : S → k) :
    (evaluate x).comp (observationMap S)=evaluate y ↔ ∀ i : S, x i=y i := by
  constructor
  · intro h i
    have he := LinearMap.congr_fun h (Finsupp.single i 1)
    simpa [observationMap, evaluate_single] using he
  · intro h
    ext i
    change evaluate x (observationMap S (Finsupp.single i 1)) =
      evaluate y (Finsupp.single i 1)
    simpa [observationMap] using h i

def coordinateFiberEquiv (y : S → k) : coordinateFiber r d S y ≃
    restrictionFiber (rowMap r) (constantMap d) (observationMap S) (evaluate y) where
  toFun x := ⟨coordinateEquiv r d x.val, (observation_equation S _ _).2 x.property⟩
  invFun f := ⟨(coordinateEquiv r d).symm f.val, by
    apply (observation_equation S _ _).1
    simpa [coordinateEquiv, evaluate] using f.property⟩
  left_inv x := by apply Subtype.ext; exact (coordinateEquiv r d).symm_apply_apply x.val
  right_inv f := by apply Subtype.ext; exact (coordinateEquiv r d).apply_symm_apply f.val

/-- Formula solely in the supplied rows, constants and observed coordinates. -/
theorem coordinate_image (y : S → k) : Nonempty (coordinateFiber r d S y) ↔
    ∀ l : J →₀ k, ∀ z : S →₀ k,
      rowMap r l=observationMap S z → constantMap d l=evaluate y z := by
  rw [← restriction_image (rowMap r) (constantMap d) (observationMap S) (evaluate y)]
  exact (coordinateFiberEquiv r d S y).nonempty_congr

/-- Every nonempty original coordinate fiber, not just an abstract homogeneous kernel. -/
def coordinateFiberParameters (y : S → k) (x0 : coordinateFiber r d S y) :
    (((I →₀ k) ⧸ (LinearMap.range (rowMap r) ⊔ LinearMap.range (observationMap S))) →ₗ[k] k)
      ≃ coordinateFiber r d S y :=
  (restrictionFiberEquiv _ _ _ _ ((coordinateFiberEquiv r d S y) x0)).trans
    (coordinateFiberEquiv r d S y).symm

theorem observation_range : LinearMap.range (observationMap (k := k) S) =
    Submodule.span k ((fun i : I => Finsupp.single i (1:k)) '' S) := by
  rw [observationMap, Finsupp.range_linearCombination]
  congr 1
  ext v
  simp

/-- The original hypotheses imply all three main classification obligations. -/
theorem complete_classification (h : finiteSolvable r d) :
    Nonempty (coordinateSolutions r d) ∧
      Nonempty ((((I →₀ k) ⧸ LinearMap.range (rowMap r)) →ₗ[k] k) ≃ coordinateSolutions r d) ∧
      ∀ (A : Set I) (y : A → k),
        (Nonempty (coordinateFiber r d A y) ↔
          ∀ l : J →₀ k, ∀ z : A →₀ k,
            rowMap r l=observationMap A z → constantMap d l=evaluate y z) ∧
        (Nonempty (coordinateFiber r d A y) →
          Nonempty ((((I →₀ k) ⧸ (LinearMap.range (rowMap r) ⊔
            LinearMap.range (observationMap A))) →ₗ[k] k) ≃ coordinateFiber r d A y)) := by
  obtain ⟨x0⟩ := global_solution r d h
  exact ⟨⟨x0⟩, ⟨coordinateParameters r d x0⟩,
    fun A y => ⟨coordinate_image r d A y, fun ⟨p⟩ => ⟨coordinateFiberParameters r d A y p⟩⟩⟩

end Coordinates
end MathGauge.LinearSystems
