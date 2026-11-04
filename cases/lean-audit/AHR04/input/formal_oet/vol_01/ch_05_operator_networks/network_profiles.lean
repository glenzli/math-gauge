import formal_oet.vol_01.ch_05_operator_networks.network_extensional_space

namespace formal_oet.vol_01.ch_05_operator_networks

open formal_oet.vol_01.ch_01_foundations

universe u v w

variable {X : Type} {bot : X}

/--
OET anchor: h-86752cb60c8e01e3
**定义（网络读出映射）**
A network profile is a selected readout from network objects to a value space.
-/
structure NetworkProfile (Net : Sort u) (P : Sort v) where
  read : Net → P

/--
OET path: vol-01-gauge-spaces-and-operators/05-operator-networks.md
**定义（网络读出映射）**
A parametrized profile records the readout parameter explicitly.
-/
structure ParametrizedNetworkProfile (Net : Sort u) (Param : Sort v) (P : Sort w) where
  read : Param → Net → P

/--
OET anchor: h-86752cb60c8e01e3
**定义（有序网络读出）**
An ordered profile equips its value space with an explicit preorder relation.
-/
structure OrderedNetworkProfile (Net : Sort u) (P : Sort v)
    extends NetworkProfile Net P where
  le : P → P → Prop
  le_refl : ∀ p : P, le p p
  le_trans : ∀ {p q r : P}, le p q → le q r → le p r

/--
OET anchor: h-86752cb60c8e01e3
**定义（规范网络读出）**
A gauge profile equips its value space with a finite family of extended
pseudometrics. The distance axioms are part of the definition; the readout
value space need not carry a distinguished absorbing point.
-/
structure GaugeNetworkProfile (Net : Sort u) (P : Sort v) (A : Type w)
    extends NetworkProfile Net P where
  dist : A → P → P → ENNReal
  finite_index : Fintype A
  dist_self : ∀ a p, dist a p p = 0
  dist_symm : ∀ a p q, dist a p q = dist a q p
  dist_triangle : ∀ a p q r, dist a p r ≤ dist a p q + dist a q r

/--
OET anchor: h-86752cb60c8e01e3
**定义（算子读出映射）**
The operator readout is the basic network profile with value space
`X_op`.
-/
noncomputable def operator_profile :
    NetworkProfile (NetworkObject X bot) (Operator X bot) where
  read := NetworkObject.extensional_operator

/--
OET anchor: h-86752cb60c8e01e3
**定义（外延不变读出）**
A profile is extensional-invariant when it is constant on operator-readout
fibers.
-/
def ExtensionalInvariantProfile
    {P : Sort v} (profile : NetworkProfile (NetworkObject X bot) P) : Prop :=
  ∀ N M : NetworkObject X bot,
    (operator_profile (X := X) (bot := bot)).read N =
      (operator_profile (X := X) (bot := bot)).read M →
    profile.read N = profile.read M

/--
OET anchor: h-86752cb60c8e01e3
**定义（外延不变读出）**
The operator profile is extensional-invariant by definition.
-/
theorem operator_profile_extensional_invariant :
    ExtensionalInvariantProfile (operator_profile (X := X) (bot := bot)) := by
  intro N M h
  exact h

end formal_oet.vol_01.ch_05_operator_networks
