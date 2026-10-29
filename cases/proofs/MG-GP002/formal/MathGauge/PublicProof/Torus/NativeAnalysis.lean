import MathGauge.PublicProof.Torus.Representation

noncomputable section
namespace MathGauge.PublicProof.Torus
open scoped Topology ContDiff
open Borrowed.TorusInverse Borrowed.SmoothFourierData

def pairProject (x : Plane) : Torus2 := ![(x.1 : UnitAddCircle), (x.2 : UnitAddCircle)]

lemma pairProject_surjective : Function.Surjective pairProject := by
  intro y
  obtain ⟨x0, h0⟩ := Quotient.exists_rep (y 0)
  obtain ⟨x1, h1⟩ := Quotient.exists_rep (y 1)
  refine ⟨(x0, x1), ?_⟩
  ext i
  fin_cases i
  · exact h0
  · exact h1

lemma coverOf_apply (u : C(Torus2, ℂ)) (x : Plane) : coverOf u x = u (pairProject x) := rfl

lemma coordinateDerivative_cover {u : Torus2 → ℂ} {g : Plane → ℂ}
    (hg : ContDiff ℝ ∞ g) (he : ∀ x, u (pairProject x) = g x) (j : Bool) (x : Plane) :
    coordinateDerivative (if j then 1 else 0) u (pairProject x) = coordinatePartial j g x := by
  cases j
  · have hd : HasDerivAt (fun t : ℝ => g (x.1 + t, x.2)) (coordinatePartial false g x) 0 := by
      apply ((hg.differentiable (by simp)) x).hasFDerivAt.comp_hasDerivAt_of_eq 0
      · simpa only [coordinatePartial, Bool.false_eq_true, ↓reduceIte] using
          ((hasDerivAt_id (0 : ℝ)).const_add x.1).prodMk (hasDerivAt_const (0 : ℝ) x.2)
      · simp
    change deriv (fun t : ℝ => u (pairProject x + project (Pi.single 0 t))) 0 = _
    have hfun : (fun t : ℝ => u (pairProject x + project (Pi.single 0 t))) =
        (fun t : ℝ => g (x.1 + t, x.2)) := by
      funext t
      rw [← he]
      congr 1
      ext i
      fin_cases i <;> simp [pairProject, project, Pi.single_apply]
    rw [hfun]
    exact hd.deriv
  · have hd : HasDerivAt (fun t : ℝ => g (x.1, x.2 + t)) (coordinatePartial true g x) 0 := by
      apply ((hg.differentiable (by simp)) x).hasFDerivAt.comp_hasDerivAt_of_eq 0
      · simpa only [coordinatePartial, ↓reduceIte] using
          (hasDerivAt_const (0 : ℝ) x.1).prodMk ((hasDerivAt_id (0 : ℝ)).const_add x.2)
      · simp
    change deriv (fun t : ℝ => u (pairProject x + project (Pi.single 1 t))) 0 = _
    have hfun : (fun t : ℝ => u (pairProject x + project (Pi.single 1 t))) =
        (fun t : ℝ => g (x.1, x.2 + t)) := by
      funext t
      rw [← he]
      congr 1
      ext i
      fin_cases i <;> simp [pairProject, project, Pi.single_apply]
    rw [hfun]
    exact hd.deriv

lemma iterateCoordinate_cover {u : Torus2 → ℂ} {g : Plane → ℂ}
    (hg : ContDiff ℝ ∞ g) (he : ∀ x, u (pairProject x) = g x) (j : Bool) (n : ℕ) :
    ∀ x, (coordinateDerivative (if j then 1 else 0))^[n] u (pairProject x) =
      derivativeWord (List.replicate n j) g x := by
  induction n with
  | zero => exact he
  | succ n ih =>
    intro x
    rw [Function.iterate_succ_apply', List.replicate_succ]
    exact coordinateDerivative_cover (derivativeWord_smooth hg _) ih j x

lemma derivativeWord_append (v w : List Bool) (f : Plane → ℂ) :
    derivativeWord (v ++ w) f = derivativeWord v (derivativeWord w f) := by
  induction v with
  | nil => rfl
  | cons j js ih => simp only [List.cons_append, derivativeWord, ih]

/-- Every prescribed mixed torus derivative agrees with the same ordered
partial derivative of the periodic cover. No permutation-of-derivatives shortcut is used. -/
theorem mixedDerivative_cover (u : C(Torus2, ℂ)) (hu : Smooth u) (a b : ℕ) (x : Plane) :
    mixedDerivative a b u (pairProject x) = orderedDerivative a b (coverOf u) x := by
  have hg := (smooth_iff_coverOf u).mp hu
  have he : ∀ x, u (pairProject x) = coverOf u x := fun _ => rfl
  have hy := iterateCoordinate_cover hg he true b
  have hx := iterateCoordinate_cover (derivativeWord_smooth hg (List.replicate b true)) hy false a x
  simpa only [mixedDerivative, Bool.false_eq_true, ↓reduceIte, orderedDerivative,
    orderedWord, derivativeWord_append] using hx

/-- Intrinsic torus directional derivatives and the genuine Fréchet derivative agree. -/
theorem transport_native_cover (u : C(Torus2, ℂ)) (hu : Smooth u) (α : ℝ) (x : Plane) :
    transport α u (pairProject x) = transportCover α (coverOf u) x := by
  rw [transport, transportCover_coordinate_formula]
  have hg := (smooth_iff_coverOf u).mp hu
  have he : ∀ x, u (pairProject x) = coverOf u x := fun _ => rfl
  have h0 := coordinateDerivative_cover hg he false x
  have h1 := coordinateDerivative_cover hg he true x
  simp only [Bool.false_eq_true, ↓reduceIte] at h0 h1
  rw [h0, h1]

def nativeCMValues (m : ℕ) (u : Torus2 → ℂ) : Set ℝ :=
  {v | ∃ a b : ℕ, a + b ≤ m ∧ ∃ y : Torus2, v = ‖mixedDerivative a b u y‖}

def nativeCNorm (m : ℕ) (u : Torus2 → ℂ) : ℝ := sSup (nativeCMValues m u)

/-- The exact task norm is preserved between the torus and periodic-cover presentations. -/
theorem nativeCNorm_eq_cover (u : C(Torus2, ℂ)) (hu : Smooth u) (m : ℕ) :
    nativeCNorm m u = cmNormCover m (coverOf u) := by
  unfold nativeCNorm cmNormCover
  congr 1
  ext v
  constructor
  · rintro ⟨a, b, hab, y, hv⟩
    obtain ⟨x, rfl⟩ := pairProject_surjective y
    exact ⟨a, b, hab, x, hv.trans (congrArg norm (mixedDerivative_cover u hu a b x))⟩
  · rintro ⟨a, b, hab, x, hv⟩
    exact ⟨a, b, hab, pairProject x, hv.trans (congrArg norm (mixedDerivative_cover u hu a b x)).symm⟩

end MathGauge.PublicProof.Torus
