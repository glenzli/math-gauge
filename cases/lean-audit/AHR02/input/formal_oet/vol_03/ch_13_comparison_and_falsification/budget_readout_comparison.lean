import formal_oet.vol_02.ch_08_network_fitting.profile_controlled_proxy
import formal_oet.vol_02.ch_10_composition_fitting.external_composition
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace formal_oet.vol_03.ch_13_comparison_and_falsification

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_04_operator_chain_calculus
open formal_oet.vol_01.ch_05_operator_networks
open formal_oet.vol_02.ch_08_network_fitting
open formal_oet.vol_02.ch_10_composition_fitting

open scoped BigOperators

variable {X I Net ProfileValue α : Type} {bot : X} [Fintype I]

/--
OET anchor: h-3a69b1cd5dda780e
**定义（经验误差带内读出前沿，经验可接受候选索引集）**
An index is empirically acceptable when its certified domain contains the
common analysis domain and its network belongs to the profile's admissible set.
-/
def empirical_acceptable_indices
    (cert_domain : α → Set X) (net : α → Net)
    (U₀ : Set X) (admissible : Set Net) : Set α :=
  {a | U₀ ⊆ cert_domain a ∧ net a ∈ admissible}

/--
OET anchor: h-1ebd1372cd7d2bb2
**命题（局部残差次序不决定传播预算）**
The exact finite scalar example from the text.
-/
theorem local_error_order_not_budget_order_example :
    ∃ tau epsA epsB coeffA coeffB : ENNReal,
      epsA < epsB ∧
        ¬ coeffA * epsA ≤ tau ∧
        coeffB * epsB ≤ tau := by
  refine ⟨3, 1, 2, 4, 1, ?_⟩
  norm_num

/--
OET anchor: h-b6d94b9dead3cb6b
**定义（经验误差带内读出前沿）**
Profile comparison between two accepted empirical candidates.
-/
def empirical_profile_le
    (Γ : OrderedNetworkProfile Net ProfileValue) (net : α → Net)
    (a b : α) : Prop :=
  profile_le Γ (net a) (net b)

/--
OET anchor: h-b6d94b9dead3cb6b
**定义（经验误差带内读出前沿）**
The canonical strict part of the empirical profile preorder between two
accepted candidates.
-/
def empirical_profile_lt
    (Γ : OrderedNetworkProfile Net ProfileValue) (net : α → Net)
    (a b : α) : Prop :=
  empirical_profile_le Γ net a b ∧ ¬ empirical_profile_le Γ net b a

/--
OET anchor: h-b6d94b9dead3cb6b
**定义（经验误差带内读出前沿）**
The empirical profile front consists of accepted indices not strictly dominated
by another accepted index.
-/
def empirical_profile_front
    (Γ : OrderedNetworkProfile Net ProfileValue)
    (cert_domain : α → Set X) (net : α → Net)
    (U₀ : Set X) (admissible : Set Net) : Set α :=
  {a | a ∈ empirical_acceptable_indices cert_domain net U₀ admissible ∧
    ¬ ∃ b ∈ empirical_acceptable_indices cert_domain net U₀ admissible,
      empirical_profile_lt Γ net b a}

/--
OET anchor: h-b6d94b9dead3cb6b
**命题（经验读出前沿的基本性质）**
The empirical profile preorder is reflexive on the accepted set and transitive
there.
-/
theorem empirical_profile_le_preorder
    (Γ : OrderedNetworkProfile Net ProfileValue)
    (cert_domain : α → Set X) (net : α → Net)
    (U₀ : Set X) (admissible : Set Net) :
    (∀ a ∈ empirical_acceptable_indices cert_domain net U₀ admissible,
        empirical_profile_le Γ net a a) ∧
      (∀ a ∈ empirical_acceptable_indices cert_domain net U₀ admissible,
        ∀ b ∈ empirical_acceptable_indices cert_domain net U₀ admissible,
          ∀ c ∈ empirical_acceptable_indices cert_domain net U₀ admissible,
            empirical_profile_le Γ net a b →
              empirical_profile_le Γ net b c →
                empirical_profile_le Γ net a c) := by
  constructor
  · intro a _ha
    exact Γ.le_refl (Γ.read (net a))
  · intro a _ha b _hb c _hc hab hbc
    exact Γ.le_trans hab hbc

/--
OET anchor: h-b6d94b9dead3cb6b
**命题（经验读出前沿的基本性质，严格支配排除）**
A strictly dominated accepted candidate is not in the empirical profile front.
-/
theorem empirical_profile_lt_not_front
    (Γ : OrderedNetworkProfile Net ProfileValue)
    (cert_domain : α → Set X) (net : α → Net)
    (U₀ : Set X) (admissible : Set Net) {a b : α}
    (ha : a ∈ empirical_acceptable_indices cert_domain net U₀ admissible)
    (hb : b ∈ empirical_acceptable_indices cert_domain net U₀ admissible)
    (hlt : empirical_profile_lt Γ net b a) :
    a ∉ empirical_profile_front Γ cert_domain net U₀ admissible := by
  have _ := ha
  intro hfront
  exact hfront.2 ⟨b, hb, hlt⟩

/--
OET anchor: h-b6d94b9dead3cb6b
**命题（经验读出前沿的基本性质，有限非空性）**
A nonempty finite accepted set has an undominated candidate.
-/
theorem empirical_profile_front_nonempty
    [Finite α]
    (Γ : OrderedNetworkProfile Net ProfileValue)
    (cert_domain : α → Set X) (net : α → Net)
    (U₀ : Set X) (admissible : Set Net)
    (hacc :
      (empirical_acceptable_indices cert_domain net U₀ admissible).Nonempty) :
    (empirical_profile_front Γ cert_domain net U₀ admissible).Nonempty := by
  letI : Preorder ProfileValue :=
    { le := Γ.le
      le_refl := Γ.le_refl
      le_trans := fun _ _ _ hab hbc => Γ.le_trans hab hbc }
  obtain ⟨a, ha⟩ :=
    (Set.toFinite
      (empirical_acceptable_indices cert_domain net U₀ admissible)).exists_minimalFor
      (fun b => Γ.read (net b))
      (empirical_acceptable_indices cert_domain net U₀ admissible)
      hacc
  refine ⟨a, ha.1, ?_⟩
  rintro ⟨b, hb, hba⟩
  exact hba.2 (ha.2 hb hba.1)

/--
OET anchor: h-b6d94b9dead3cb6b
**命题（经验读出前沿的基本性质，正文前提版本）**
The text-level wrapper retains the finite nonempty candidate family, nonempty
component set, finite tolerance, and pointwise soundness of each certified set.
-/
theorem empirical_profile_front_basic_properties_text
    [Fintype α] [Nonempty α]
    (d : I → X → X → ENNReal)
    (target : Operator X bot)
    (operator_readout : Net → Operator X bot)
    (Γ : OrderedNetworkProfile Net ProfileValue)
    (cert_domain : α → Set X) (net : α → Net)
    (U₀ : Set X) (J : Set I) (tau : I → ENNReal)
    (admissible : Set Net)
    (hJ_nonempty : J.Nonempty)
    (htau_finite : ∀ j : I, j ∈ J → tau j ≠ ⊤)
    (hcert_dom : ∀ a : α, cert_domain a ⊆
      dom (operator_readout (net a)) ∩ dom target)
    (hcert :
      ∀ a : α, ∀ x ∈ cert_domain a, ∀ j : I, j ∈ J →
        d j ((operator_readout (net a)).func x) (target.func x) ≤ tau j) :
    ((∀ a ∈ empirical_acceptable_indices cert_domain net U₀ admissible,
        empirical_profile_le Γ net a a) ∧
      (∀ a ∈ empirical_acceptable_indices cert_domain net U₀ admissible,
        ∀ b ∈ empirical_acceptable_indices cert_domain net U₀ admissible,
          ∀ c ∈ empirical_acceptable_indices cert_domain net U₀ admissible,
            empirical_profile_le Γ net a b →
              empirical_profile_le Γ net b c →
                empirical_profile_le Γ net a c)) ∧
      (∀ a b : α,
        a ∈ empirical_acceptable_indices cert_domain net U₀ admissible →
        b ∈ empirical_acceptable_indices cert_domain net U₀ admissible →
        empirical_profile_lt Γ net b a →
        a ∉ empirical_profile_front Γ cert_domain net U₀ admissible) ∧
      ((empirical_acceptable_indices cert_domain net U₀ admissible).Nonempty →
        (empirical_profile_front Γ cert_domain net U₀ admissible).Nonempty) := by
  have _ := hJ_nonempty
  have _ := htau_finite
  have _ := hcert_dom
  have _ := hcert
  constructor
  · exact empirical_profile_le_preorder Γ cert_domain net U₀ admissible
  · constructor
    · intro a b ha hb hlt
      exact empirical_profile_lt_not_front Γ cert_domain net U₀ admissible
        ha hb hlt
    · exact empirical_profile_front_nonempty Γ cert_domain net U₀ admissible

/-- A candidate accepted by the empirical front has valid outputs and the
specified pointwise error bound on the common analysis domain. -/
theorem empirical_accepted_candidate_sound
    (d : I → X → X → ENNReal)
    (target : Operator X bot)
    (operator_readout : Net → Operator X bot)
    (cert_domain : α → Set X) (net : α → Net)
    (U₀ : Set X) (J : Set I) (tau : I → ENNReal)
    (admissible : Set Net)
    (hcert_dom : ∀ a : α, cert_domain a ⊆
      dom (operator_readout (net a)) ∩ dom target)
    (hcert : ∀ a : α, ∀ x ∈ cert_domain a, ∀ j ∈ J,
      d j ((operator_readout (net a)).func x) (target.func x) ≤ tau j)
    {a : α}
    (ha : a ∈ empirical_acceptable_indices cert_domain net U₀ admissible) :
    U₀ ⊆ dom (operator_readout (net a)) ∩ dom target ∧
      ∀ x ∈ U₀, ∀ j ∈ J,
        d j ((operator_readout (net a)).func x) (target.func x) ≤ tau j := by
  exact ⟨fun _ hx => hcert_dom a (ha.1 hx),
    fun x hx j hj => hcert a x (ha.1 hx) j hj⟩

end formal_oet.vol_03.ch_13_comparison_and_falsification
