import Transfer
namespace MathGauge.F101
variable {R : Type*} [CommRing R]
theorem candidate_nilpotent (I : Ideal R) (d : SourceData I) (n : ℕ) :
    IsNilpotent (residual I n) := transport I (I ^ (n + 1)) d
theorem candidate_transition (I : Ideal R) {m n : ℕ} (h : m ≤ n) :
    (residual I n).map (transition I h) = residual I m := transition_image I h
theorem candidate_composition (I : Ideal R) {l m n : ℕ} (h : l ≤ m) (k : m ≤ n) :
    (transition I h).comp (transition I k) = transition I (h.trans k) :=
  transition_comp I h k
#print axioms candidate_nilpotent
#print axioms candidate_transition
#print axioms candidate_composition
end MathGauge.F101
