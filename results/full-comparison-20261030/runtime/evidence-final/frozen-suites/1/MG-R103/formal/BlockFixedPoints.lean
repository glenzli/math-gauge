import Mathlib.Order.FixedPoints
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Tactic

namespace MathGauge.R103

variable {P A B C D : Type*}

section Parameter
variable [Preorder P] [CompleteLattice A]

/-- Freeze only the external parameter of a jointly monotone update. -/
def slice (F : P × A →o A) (p : P) : A →o A where
  toFun a := F (p, a)
  monotone' _ _ h := F.monotone ⟨le_rfl, h⟩

/-- The parameterized least solution, on the actual complete lattice. -/
def solve (F : P × A →o A) : P →o A where
  toFun p := (slice F p).lfp
  monotone' _ _ hp := OrderHom.lfp.monotone (fun _ => F.monotone ⟨hp, le_rfl⟩)

theorem solve_fixed (F : P × A →o A) (p : P) :
    F (p, solve F p) = solve F p := (slice F p).map_lfp

theorem solve_le_prefixed (F : P × A →o A) (p : P) (a : A)
    (ha : F (p, a) ≤ a) : solve F p ≤ a := (slice F p).lfp_le ha

end Parameter

section Blocks
variable [CompleteLattice A] [CompleteLattice B]

/-- Solve the second block with the first block still variable. -/
def inner (G : A × B →o B) : A →o B := solve G

/-- Substitute the second block's least solution into the first update. -/
def reduced (F : A × B →o A) (G : A × B →o B) : A →o A where
  toFun a := F (a, inner G a)
  monotone' _ _ h := F.monotone ⟨h, (inner G).monotone h⟩

def joint (F : A × B →o A) (G : A × B →o B) : A × B →o A × B where
  toFun z := (F z, G z)
  monotone' _ _ h := ⟨F.monotone h, G.monotone h⟩

def assembled (F : A × B →o A) (G : A × B →o B) : A × B :=
  ((reduced F G).lfp, inner G (reduced F G).lfp)

theorem assembled_fixed (F : A × B →o A) (G : A × B →o B) :
    joint F G (assembled F G) = assembled F G := by
  apply Prod.ext
  · exact (reduced F G).map_lfp
  · exact solve_fixed G _

theorem assembled_le_prefixed (F : A × B →o A) (G : A × B →o B)
    (z : A × B) (hz : joint F G z ≤ z) : assembled F G ≤ z := by
  have hy : inner G z.1 ≤ z.2 := solve_le_prefixed G z.1 z.2 hz.2
  have hFa : F (z.1, inner G z.1) ≤ F z := F.monotone ⟨le_rfl, hy⟩
  have hx : (reduced F G).lfp ≤ z.1 :=
    (reduced F G).lfp_le (hFa.trans hz.1)
  exact ⟨hx, ((inner G).monotone hx).trans hy⟩

/-- Bekić elimination proved through least prefixed points, without sequential continuity. -/
theorem assembled_eq_lfp (F : A × B →o A) (G : A × B →o B) :
    assembled F G = (joint F G).lfp := by
  exact le_antisymm
    (assembled_le_prefixed F G _ (joint F G).map_lfp.le)
    ((joint F G).lfp_le (assembled_fixed F G).le)

end Blocks

section Triple
variable [Preorder P] [CompleteLattice A] [CompleteLattice B] [CompleteLattice C]

/-- The genuine three-block update, with parameter p. -/
def triple_update (F : P × (A × (B × C)) →o A)
    (G : P × (A × (B × C)) →o B) (H : P × (A × (B × C)) →o C) :
    P × (A × (B × C)) →o A × (B × C) where
  toFun z := (F z, G z, H z)
  monotone' _ _ h := ⟨F.monotone h, G.monotone h, H.monotone h⟩

def first_update (F : P × (A × (B × C)) →o A) (p : P) :
    A × (B × C) →o A where
  toFun z := F (p,z)
  monotone' _ _ h := F.monotone ⟨le_rfl,h⟩

def rest_update (G : P × (A × (B × C)) →o B)
    (H : P × (A × (B × C)) →o C) (p : P) :
    A × (B × C) →o B × C where
  toFun z := (G (p,z), H (p,z))
  monotone' _ _ h := ⟨G.monotone ⟨le_rfl,h⟩, H.monotone ⟨le_rfl,h⟩⟩

def second_update (G : P × (A × (B × C)) →o B) (p : P) (a : A) :
    B × C →o B where
  toFun z := G (p,a,z)
  monotone' _ _ h := G.monotone ⟨le_rfl,le_rfl,h⟩

def third_update (H : P × (A × (B × C)) →o C) (p : P) (a : A) :
    B × C →o C where
  toFun z := H (p,a,z)
  monotone' _ _ h := H.monotone ⟨le_rfl,le_rfl,h⟩

/-- The outer elimination returns exactly the simultaneous least three-block solution. -/
theorem triple_elimination (F : P × (A × (B × C)) →o A)
    (G : P × (A × (B × C)) →o B) (H : P × (A × (B × C)) →o C) (p : P) :
    assembled (first_update F p) (rest_update G H p) =
      solve (triple_update F G H) p := by
  exact assembled_eq_lfp _ _

/-- The inner two-block solution is itself obtained by valid elimination. -/
theorem inner_elimination (G : P × (A × (B × C)) →o B)
    (H : P × (A × (B × C)) →o C) (p : P) (a : A) :
    assembled (second_update G p a) (third_update H p a) =
      inner (rest_update G H p) a := by
  exact assembled_eq_lfp _ _

end Triple

section Transport
variable [CompleteLattice A] [CompleteLattice B]

/-- Exact least-solution transport needs the actual adjunction, not just monotonicity. -/
theorem lfp_transport (F : A →o A) (G : B →o B)
    (alpha : A →o B) (gamma : B →o A)
    (adj : GaloisConnection alpha gamma)
    (comm : ∀ a, alpha (F a) = G (alpha a)) :
    alpha F.lfp = G.lfp := by
  apply le_antisymm
  · apply (adj _ _).mpr
    apply F.lfp_le
    apply (adj _ _).mp
    rw [comm]
    exact (G.monotone (adj.l_u_le G.lfp)).trans G.map_lfp.le
  · apply G.lfp_le
    rw [← comm, F.map_lfp]

theorem parameter_transport [Preorder P]
    (F : P × A →o A) (G : P × B →o B)
    (alpha : A →o B) (gamma : B →o A)
    (adj : GaloisConnection alpha gamma)
    (comm : ∀ p a, alpha (F (p,a)) = G (p,alpha a)) (p : P) :
    alpha (solve F p) = solve G p :=
  lfp_transport (slice F p) (slice G p) alpha gamma adj (comm p)

/-- Regrouping or permuting blocks is an order-isomorphic change of coordinates. -/
theorem coordinate_transport (F : A →o A) (e : A ≃o B) :
    e F.lfp = (e.toOrderEmbedding.toOrderHom.comp (F.comp e.symm.toOrderEmbedding.toOrderHom)).lfp := by
  apply lfp_transport F _ e.toOrderEmbedding.toOrderHom e.symm.toOrderEmbedding.toOrderHom
  · intro a b
    exact e.le_symm_apply.symm
  · intro a
    simp

end Transport

section Integration
variable [Preorder P] [CompleteLattice A] [CompleteLattice B]
  [CompleteLattice C] [CompleteLattice D]

/-- The concrete three-block eliminated result also satisfies exact abstract transport. -/
theorem elimination_transport
    (F : P × (A × (B × C)) →o A)
    (G : P × (A × (B × C)) →o B) (H : P × (A × (B × C)) →o C)
    (K : P × D →o D) (alpha : A × (B × C) →o D)
    (gamma : D →o A × (B × C)) (adj : GaloisConnection alpha gamma)
    (comm : ∀ p x, alpha (triple_update F G H (p,x)) = K (p,alpha x)) (p : P) :
    alpha (assembled (first_update F p) (rest_update G H p)) = solve K p := by
  rw [triple_elimination]
  exact parameter_transport (triple_update F G H) K alpha gamma adj comm p

/-- Every order-isomorphic division into two blocks has the same eliminated result. -/
theorem regrouped_elimination (T : A →o A) (e : A ≃o B × C) :
    let K := e.toOrderEmbedding.toOrderHom.comp (T.comp e.symm.toOrderEmbedding.toOrderHom)
    let f : B × C →o B := ⟨fun x => (K x).1, fun _ _ h => (K.monotone h).1⟩
    let g : B × C →o C := ⟨fun x => (K x).2, fun _ _ h => (K.monotone h).2⟩
    e T.lfp = assembled f g := by
  dsimp only
  rw [assembled_eq_lfp]
  exact coordinate_transport T e

end Integration

end MathGauge.R103
