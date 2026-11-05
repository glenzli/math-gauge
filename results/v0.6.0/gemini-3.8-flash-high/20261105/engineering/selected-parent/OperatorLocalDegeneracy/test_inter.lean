import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Finset.Basic

variable {ι : Type} [DecidableEq ι]

lemma sSup_inter_eq_min (s : ι → Set ENNReal) (M : ι → ENNReal)
    (h_down : ∀ i, ∀ r ∈ s i, ∀ r', 0 < r' → r' ≤ r → r' ∈ s i)
    (h_sup : ∀ i, sSup (s i) = M i)
    (J : Finset ι) (hJ : J.Nonempty) :
    sSup (⋂ i ∈ J, s i) = J.inf' hJ M := by
  sorry
