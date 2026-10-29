import Core

noncomputable section
namespace MathGauge.RecursiveClosure
variable {X I : Type} (bot : X)

/-- Canonical equivalence between the given absorbing-point space and the formal Option encoding. -/
def absorbingEquiv : Option {x : X // x≠bot} ≃ X where
  toFun := fun x => match x with | none => bot | some y => y.val
  invFun x := by
    classical
    exact if h : x=bot then none else some ⟨x,h⟩
  left_inv := by
    classical
    intro x
    cases x with
    | none => simp
    | some y => simp [y.property]
  right_inv := by
    classical
    intro x
    dsimp only
    split_ifs with h
    · exact h.symm
    · rfl

variable (d : I → X → X → ENNReal)
variable (hself : ∀ i x, d i x x=0) (hsymm : ∀ i x y, d i x y=d i y x)
variable (htriangle : ∀ i x y z, d i x z ≤ d i x y+d i y z)
variable (hisolated : ∀ i x, x≠bot → d i x bot=⊤)

def restrictedGauge : Gauge {x : X // x≠bot} I where
  d i x y := d i x.val y.val
  self i x := hself i x.val
  symm i x y := hsymm i x.val y.val
  triangle i x y z := htriangle i x.val y.val z.val

include hisolated in
theorem absorbing_distance_transport (i : I) (x y : Option {x : X // x≠bot}) :
    liftDistance (restrictedGauge bot d hself hsymm htriangle) i x y=
      d i (absorbingEquiv bot x) (absorbingEquiv bot y) := by
  cases x with
  | none =>
    cases y with
    | none => exact (hself i bot).symm
    | some y => exact ((hsymm i bot y.val).trans (hisolated i y.val y.property)).symm
  | some x =>
    cases y with
    | none => exact (hisolated i x.val x.property).symm
    | some y => rfl

end MathGauge.RecursiveClosure
