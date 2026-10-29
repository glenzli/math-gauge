import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
MG-R005: nonnegative extended convex costs on arbitrary real locally convex spaces.
The real epigraph includes the nonnegativity condition on its height, so a cost of
zero has the correct epigraph even at negative heights.
-/
noncomputable section

open Set
open scoped ENNReal

namespace MathGauge.ConvexCost

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def epigraph (f : E → ℝ≥0∞) : Set (E × ℝ) :=
  {p | 0 ≤ p.2 ∧ f p.1 ≤ ENNReal.ofReal p.2}

def ConvexCost (f : E → ℝ≥0∞) : Prop := Convex ℝ (epigraph f)

def JensenConvex (f : E → ℝ≥0∞) : Prop :=
  ∀ x y a b, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ ENNReal.ofReal a * f x + ENNReal.ofReal b * f y

theorem convexCost_of_jensen {f : E → ℝ≥0∞} (hf : JensenConvex f) : ConvexCost f := by
  intro p hp q hq a b ha hb hab
  have ht : 0 ≤ a * p.2 + b * q.2 := add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1)
  refine ⟨ht, ?_⟩
  change f (a • p.1 + b • q.1) ≤ ENNReal.ofReal (a * p.2 + b * q.2)
  calc
    _ ≤ ENNReal.ofReal a * f p.1 + ENNReal.ofReal b * f q.1 := hf _ _ _ _ ha hb hab
    _ ≤ ENNReal.ofReal a * ENNReal.ofReal p.2 +
        ENNReal.ofReal b * ENNReal.ofReal q.2 :=
      add_le_add (mul_le_mul_left' hp.2 _) (mul_le_mul_left' hq.2 _)
    _ = _ := by rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hb,
      ENNReal.ofReal_add (mul_nonneg ha hp.1) (mul_nonneg hb hq.1)]

theorem jensen_of_convexCost {f : E → ℝ≥0∞} (hf : ConvexCost f) : JensenConvex f := by
  intro x y a b ha hb hab
  by_cases ha0 : a = 0
  · subst a
    have : b = 1 := by linarith
    subst b
    simp
  by_cases hb0 : b = 0
  · subst b
    have : a = 1 := by linarith
    subst a
    simp
  by_cases hx : f x = ⊤
  · have hapos : 0 < ENNReal.ofReal a := ENNReal.ofReal_pos.mpr (lt_of_le_of_ne ha (Ne.symm ha0))
    simp [hx, hapos.ne']
  by_cases hy : f y = ⊤
  · have hbpos : 0 < ENNReal.ofReal b := ENNReal.ofReal_pos.mpr (lt_of_le_of_ne hb (Ne.symm hb0))
    simp [hy, hbpos.ne']
  have hx' : (x, (f x).toReal) ∈ epigraph f :=
    ⟨ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hx).ge⟩
  have hy' : (y, (f y).toReal) ∈ epigraph f :=
    ⟨ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hy).ge⟩
  have h := (hf hx' hy' ha hb hab).2
  change f (a • x + b • y) ≤ ENNReal.ofReal (a * (f x).toReal + b * (f y).toReal) at h
  convert h using 1
  rw [ENNReal.ofReal_add (mul_nonneg ha ENNReal.toReal_nonneg)
    (mul_nonneg hb ENNReal.toReal_nonneg), ENNReal.ofReal_mul ha,
    ENNReal.ofReal_mul hb, ENNReal.ofReal_toReal hx, ENNReal.ofReal_toReal hy]

theorem convexCost_iff_jensen (f : E → ℝ≥0∞) : ConvexCost f ↔ JensenConvex f :=
  ⟨jensen_of_convexCost, convexCost_of_jensen⟩

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem closed_epigraph {f : E → ℝ≥0∞} (hf : LowerSemicontinuous f) :
    IsClosed (epigraph f) := by
  have hc : Continuous (fun p : E × ℝ => (p.1, ENNReal.ofReal p.2)) :=
    continuous_fst.prodMk (ENNReal.continuous_ofReal.comp continuous_snd)
  exact (isClosed_le continuous_const continuous_snd).inter (hf.isClosed_epigraph.preimage hc)

def affineHull (f : E → ℝ≥0∞) (x : E) : ℝ≥0∞ :=
  ⨆ (l : E →L[ℝ] ℝ) (b : ℝ) (_ : ∀ z, ENNReal.ofReal (l z + b) ≤ f z),
    ENNReal.ofReal (l x + b)

theorem affineHull_le (f : E → ℝ≥0∞) : affineHull f ≤ f := by
  intro x
  exact iSup_le fun l => iSup_le fun b => iSup_le fun h => h x

theorem affineHull_mono {f g : E → ℝ≥0∞} (h : f ≤ g) : affineHull f ≤ affineHull g := by
  intro x
  exact iSup_le fun l => iSup_le fun b => iSup_le fun hl =>
    le_iSup_of_le l <| le_iSup_of_le b <| le_iSup_of_le (fun z => (hl z).trans (h z)) le_rfl

theorem affine_minorant_le_hull {f : E → ℝ≥0∞} (l : E →L[ℝ] ℝ) (b : ℝ)
    (h : ∀ z, ENNReal.ofReal (l z + b) ≤ f z) (x : E) :
    ENNReal.ofReal (l x + b) ≤ affineHull f x :=
  le_iSup_of_le l <| le_iSup_of_le b <| le_iSup_of_le h le_rfl

theorem affineHull_lowerSemicontinuous (f : E → ℝ≥0∞) : LowerSemicontinuous (affineHull f) := by
  apply lowerSemicontinuous_iSup
  intro l
  apply lowerSemicontinuous_iSup
  intro b
  apply lowerSemicontinuous_iSup
  intro h
  exact (ENNReal.continuous_ofReal.comp (l.continuous.add continuous_const)).lowerSemicontinuous

theorem affineHull_convex (f : E → ℝ≥0∞) : ConvexCost (affineHull f) := by
  intro p hp q hq a b ha hb hab
  refine ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1), ?_⟩
  apply iSup_le
  intro l
  apply iSup_le
  intro c
  apply iSup_le
  intro hl
  have hp' : l p.1 + c ≤ p.2 := (ENNReal.ofReal_le_ofReal_iff hp.1).mp
    ((affine_minorant_le_hull l c hl p.1).trans hp.2)
  have hq' : l q.1 + c ≤ q.2 := (ENNReal.ofReal_le_ofReal_iff hq.1).mp
    ((affine_minorant_le_hull l c hl q.1).trans hq.2)
  apply ENNReal.ofReal_le_ofReal
  change l (a • p.1 + b • q.1) + c ≤ a * p.2 + b * q.2
  simp only [map_add, map_smul, smul_eq_mul]
  nlinarith [mul_le_mul_of_nonneg_left hp' ha, mul_le_mul_of_nonneg_left hq' hb,
    congrArg (fun z : ℝ => z * c) hab]

variable [LocallyConvexSpace ℝ E]

/-- Strict affine separation from the closed epigraph of a proper extended cost. -/
theorem exists_affine_minorant_gt_of_not_mem_closure {f : E → ℝ≥0∞} (hf : ConvexCost f)
    (hp : ∃ z, f z ≠ ⊤) {x : E} {t : ℝ} (hxt : (x,t) ∉ closure (epigraph f)) :
    ∃ (l : E →L[ℝ] ℝ) (b : ℝ),
      (∀ z, ENNReal.ofReal (l z + b) ≤ f z) ∧ t < l x + b := by
  obtain ⟨L, c, hxc, hsep₀⟩ := geometric_hahn_banach_point_closed hf.closure isClosed_closure hxt
  have hsep (p) (hp : p ∈ epigraph f) := hsep₀ p (subset_closure hp)
  let l := L.comp (ContinuousLinearMap.inl ℝ E ℝ)
  let β := L (0, 1)
  have hsplit (z : E) (s : ℝ) : L (z, s) = l z + β * s := by
    have hp : (z, s) = (z, (0 : ℝ)) + s • ((0 : E), (1 : ℝ)) := by simp
    rw [hp, map_add, map_smul]
    simp [l, β, mul_comm]
  obtain ⟨z₀, hz₀⟩ := hp
  let s₀ := (f z₀).toReal
  have hs₀ : 0 ≤ s₀ := ENNReal.toReal_nonneg
  have hzmem : (z₀, s₀) ∈ epigraph f := ⟨hs₀, (ENNReal.ofReal_toReal hz₀).ge⟩
  have hbase := hsep (z₀, s₀) hzmem
  rw [hsplit] at hbase
  have hβ : 0 ≤ β := by
    by_contra hn
    have hn' : β < 0 := lt_of_not_ge hn
    let s := (l z₀ + β * s₀ - c + 1) / (-β)
    have hs : 0 ≤ s := div_nonneg (by linarith) (neg_pos.mpr hn').le
    have hsmem : (z₀, s₀ + s) ∈ epigraph f :=
      ⟨add_nonneg hs₀ hs, hzmem.2.trans (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right hs))⟩
    have hh := hsep (z₀, s₀ + s) hsmem
    rw [hsplit] at hh
    have hid : (-β) * s = l z₀ + β * s₀ - c + 1 := by
      dsimp [s]
      field_simp [ne_of_lt hn']
    nlinarith
  rw [hsplit] at hxc
  obtain ⟨ε, hε, hεt⟩ := exists_pos_mul_lt (sub_pos.mpr hxc) t
  let γ := β + ε
  have hγ : 0 < γ := add_pos_of_nonneg_of_pos hβ hε
  have hsep' (z : E) (s : ℝ) (hs : (z,s) ∈ epigraph f) : c ≤ l z + γ * s := by
    have hh := hsep (z,s) hs
    rw [hsplit] at hh
    dsimp [γ]
    nlinarith [mul_nonneg hε.le hs.1]
  refine ⟨(-γ⁻¹) • l, c / γ, ?_, ?_⟩
  · intro z
    by_cases hz : f z = ⊤
    · simp [hz]
    have hhz := hsep' z (f z).toReal ⟨ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hz).ge⟩
    rw [← ENNReal.ofReal_toReal hz]
    apply ENNReal.ofReal_le_ofReal
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hid : (-γ⁻¹) * l z + c / γ = (c - l z) / γ := by ring
    rw [hid, div_le_iff₀ hγ]
    linarith
  · simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hid : (-γ⁻¹) * l x + c / γ = (c - l x) / γ := by ring
    rw [hid, lt_div_iff₀ hγ]
    dsimp [γ]
    nlinarith

/-- Strict real affine separation for a proper lower semicontinuous extended cost. -/
theorem exists_affine_minorant_gt {f : E → ℝ≥0∞} (hf : ConvexCost f)
    (hc : LowerSemicontinuous f) (hp : ∃ z, f z ≠ ⊤)
    {x : E} {t : ℝ} (hxt : ENNReal.ofReal t < f x) :
    ∃ (l : E →L[ℝ] ℝ) (b : ℝ),
      (∀ z, ENNReal.ofReal (l z + b) ≤ f z) ∧ t < l x + b := by
  apply exists_affine_minorant_gt_of_not_mem_closure hf hp
  rw [(closed_epigraph hc).closure_eq]
  exact fun h => hxt.not_ge h.2

/-- The affine construction is the greatest lower semicontinuous convex minorant. -/
theorem affineHull_maximal {f h : E → ℝ≥0∞} (hf : ∃ z, f z ≠ ⊤)
    (hc : LowerSemicontinuous h) (hv : ConvexCost h) (hh : h ≤ f) : h ≤ affineHull f := by
  intro x
  by_contra hn
  have hx : affineHull f x < h x := lt_of_not_ge hn
  obtain ⟨t, ht, htx, hxt⟩ := ENNReal.lt_iff_exists_real_btwn.mp hx
  have hp : ∃ z, h z ≠ ⊤ := by
    obtain ⟨z,hz⟩ := hf
    exact ⟨z, ne_top_of_le_ne_top hz (hh z)⟩
  obtain ⟨l,b,hl,hgt⟩ := exists_affine_minorant_gt hv hc hp hxt
  have hminor (z) := (hl z).trans (hh z)
  have hle := affine_minorant_le_hull l b hminor x
  have hg : ENNReal.ofReal t ≤ ENNReal.ofReal (l x + b) := ENNReal.ofReal_le_ofReal hgt.le
  exact htx.not_ge (hg.trans hle)

theorem affineHull_idempotent (f : E → ℝ≥0∞) (hp : ∃ z, f z ≠ ⊤) :
    affineHull (affineHull f) = affineHull f := by
  apply le_antisymm (affineHull_le _)
  apply affineHull_maximal
  · obtain ⟨z,hz⟩ := hp
    exact ⟨z, ne_top_of_le_ne_top hz (affineHull_le f z)⟩
  · exact affineHull_lowerSemicontinuous f
  · exact affineHull_convex f
  · exact le_rfl

/-- The affine construction is exactly the function with closed epigraph. -/
theorem epigraph_affineHull_eq_closure {f : E → ℝ≥0∞} (hf : ConvexCost f)
    (hp : ∃ z, f z ≠ ⊤) : epigraph (affineHull f) = closure (epigraph f) := by
  apply Set.Subset.antisymm
  · intro p hp'
    by_contra hn
    obtain ⟨l,b,hl,hgt⟩ := exists_affine_minorant_gt_of_not_mem_closure hf hp hn
    have hle : ENNReal.ofReal (l p.1 + b) ≤ ENNReal.ofReal p.2 :=
      (affine_minorant_le_hull l b hl p.1).trans hp'.2
    exact hgt.not_ge ((ENNReal.ofReal_le_ofReal_iff hp'.1).mp hle)
  · apply closure_minimal
    · intro p hp'
      exact ⟨hp'.1, (affineHull_le f p.1).trans hp'.2⟩
    · exact closed_epigraph (affineHull_lowerSemicontinuous f)

end MathGauge.ConvexCost
