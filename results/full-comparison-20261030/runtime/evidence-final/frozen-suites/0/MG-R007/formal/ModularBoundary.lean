import BoundaryData

noncomputable section
open Representation
namespace MathGauge.TowerBoundaries
universe u
variable (p : ℕ) [Fact p.Prime]
variable (k : Type u) [Field k] [CharP k p]

/-- The cyclic group of prime order acts by the actual unipotent shear in any field of characteristic p. -/
def primeRep : Representation k (Multiplicative (ZMod p)) (k × k) where
  toFun g :=
    { toFun x := (x.1+(ZMod.castHom (dvd_refl p) k (Multiplicative.toAdd g))*x.2,x.2)
      map_add' := by intros; ext <;> simp [mul_add]; ring
      map_smul' := by intros; ext <;> simp [mul_add]; ring }
  map_one' := by ext <;> simp
  map_mul' := by intro g h; ext <;> simp [map_add,add_mul] <;> ring

def primeQuotient : (primeRep p k).IntertwiningMap
    (Representation.trivial k (Multiplicative (ZMod p)) k) where
  toLinearMap := LinearMap.snd k k k
  isIntertwining' _ := rfl

def primeInclusion : (Representation.trivial k (Multiplicative (ZMod p)) k).IntertwiningMap
    (primeRep p k) where
  toLinearMap := LinearMap.inl k k k
  isIntertwining' := by
    intro g; apply LinearMap.ext; intro c
    change (c,0)=(c+_*0,0)
    simp

theorem prime_row : Function.Injective (primeInclusion p k) ∧
    LinearMap.range (primeInclusion p k).toLinearMap=LinearMap.ker (primeQuotient p k).toLinearMap ∧
    Function.Surjective (primeQuotient p k) := product_row

theorem no_prime_section : ¬∃ s :
    (Representation.trivial k (Multiplicative (ZMod p)) k).IntertwiningMap (primeRep p k),
    (primeQuotient p k).comp s=IntertwiningMap.id _ := by
  rintro ⟨s,hs⟩
  have hq := congrArg (fun f : (Representation.trivial k (Multiplicative (ZMod p)) k).IntertwiningMap _ => f 1) hs
  change (s 1).2=1 at hq
  have hh := IntertwiningMap.isIntertwining _ _ s (Multiplicative.ofAdd (1:ZMod p)) 1
  have hfst := congrArg Prod.fst hh
  change (s 1).1=(s 1).1+(ZMod.castHom (dvd_refl p) k (1:ZMod p))*(s 1).2 at hfst
  rw [show (ZMod.castHom (dvd_refl p) k) (1:ZMod p) = (1:k) from (ZMod.castHom (dvd_refl p) k).map_one, hq,one_mul] at hfst
  have hbad : (1:k)=0 := add_left_cancel (show (s 1).1+1=(s 1).1+0 by simpa using hfst.symm)
  exact one_ne_zero hbad

end MathGauge.TowerBoundaries
