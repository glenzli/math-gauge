import Chapter3.Models

namespace Chapter3.Rearrangement
open Chapter3
open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds
open Set
noncomputable section
open scoped Classical
def U : Set (Option ℝ) := {some 0,some 1,some 2,some 3}
def f : Operator (Option ℝ) none := ⟨fun x =>
  if x ∈ U then x else none, by simp [U]⟩
def g : Operator (Option ℝ) none := ⟨fun x =>
  if x = some 0 then some 0 else if x = some 1 then some 3 else
  if x = some 2 then some 1 else if x = some 3 then some 2 else none, by simp⟩

theorem domain : U ⊆ dom f ∧ U ⊆ dom g := by
  constructor <;> intro x hx <;> rcases hx with rfl | rfl | rfl | rfl <;> simp [dom,f,g,U]
theorem outside : ∀ x ∉ U, f.func x = none ∧ g.func x = none := by
  intro x hx
  have hh : x ≠ some 0 ∧ x ≠ some 1 ∧ x ≠ some 2 ∧ x ≠ some 3 := by simpa [U] using hx
  simp [f,g,hx,hh.1,hh.2.1,hh.2.2.1,hh.2.2.2]
theorem images : f.func '' U = U ∧ g.func '' U = U := by
  constructor
  · norm_num [f,U,image_insert_eq,image_singleton]
  · norm_num [g,U,image_insert_eq,image_singleton]
    ext x; simp; tauto

theorem covers {eps : ENNReal} (he : 0 < eps) (hef : eps < ⊤) :
    covering_number realDistance eps U = if eps ≤ 1 then 4 else if eps ≤ 2 then 2 else 1 := by
  classical
  by_cases h1 : eps ≤ 1
  · rw [if_pos h1]
    have hc := cover_separated realDistance eps ({some 0,some 1,some 2,some 3} : Finset (Option ℝ))
      he realDistance_metric.dist_self (by
        intro x hx y hy hxy
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl | rfl <;>
          rcases hy with rfl | rfl | rfl | rfl <;> norm_num at *
        all_goals exfalso; exact (not_lt_of_ge (h1.trans (by norm_num))) hxy)
    simpa [U] using hc
  · rw [if_neg h1]
    have he1 : (1 : ENNReal) < eps := lt_of_not_ge h1
    by_cases h2 : eps ≤ 2
    · rw [if_pos h2]
      apply le_antisymm
      · have hn : InternalEpsilonNet realDistance eps U {some 1,some 2} := by
          norm_num [InternalEpsilonNet,U,Set.insert_subset_iff,he1,he]
        simpa using cover_le_net _ _ _ _ hn
      · apply cover_two_lower _ _ _ ⟨some 0,by simp [U]⟩
        intro c hc
        rcases hc with rfl | rfl | rfl | rfl
        · exact ⟨some 3,by simp [U],h2.trans (by norm_num)⟩
        · exact ⟨some 3,by simp [U],h2.trans (by norm_num)⟩
        · exact ⟨some 0,by simp [U],h2.trans (by norm_num)⟩
        · exact ⟨some 0,by simp [U],h2.trans (by norm_num)⟩
    · rw [if_neg h2]
      have he2 : (2 : ENNReal) < eps := lt_of_not_ge h2
      apply le_antisymm _ (one_le_covering_number_of_nonempty _ _ _ ⟨some 0,by simp [U]⟩)
      have hn : InternalEpsilonNet realDistance eps U {some 1} := by
        norm_num [InternalEpsilonNet,U,Set.insert_subset_iff,he1,he2,he]
      simpa using cover_le_net _ _ _ _ hn

theorem internal_center : some (3/2 : ℝ) ∉ U ∧
    ¬ InternalEpsilonNet realDistance (7/4) U {some (3/2)} ∧
    (∀ x ∈ U, realDistance x (some (3/2)) < 7/4) := by
  have hc : (7 : ENNReal)/4 = ENNReal.ofReal ((7 : ℝ)/4) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  refine ⟨by norm_num [U],?_,?_⟩
  · norm_num [InternalEpsilonNet,U]
  · rw [hc]
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl <;>
      norm_num [ENNReal.ofReal_lt_ofReal_iff]

theorem lip_constants :
    HasScalarLipBound (fun _ : Unit => realDistance) f U () () 1 ∧
    HasScalarLipBound (fun _ : Unit => realDistance) g U () () 3 ∧
    (∀ L, HasScalarLipBound (fun _ : Unit => realDistance) f U () () L → 1 ≤ L) ∧
    (∀ L, HasScalarLipBound (fun _ : Unit => realDistance) g U () () L → 3 ≤ L) := by
  refine ⟨⟨domain.1,?_⟩,⟨domain.2,?_⟩,?_,?_⟩
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      norm_num [f,U]
  · intro x hx y hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      norm_num [g,U]
  · intro L h
    have hh := h.2 (some 0) (by simp [U]) (some 1) (by simp [U])
    simpa [f,U] using hh
  · intro L h
    have hh := h.2 (some 0) (by simp [U]) (some 1) (by simp [U])
    simpa [g,U] using hh

theorem equal_covers {eps : ENNReal} (he : 0 < eps) (hef : eps < ⊤) :
    covering_number realDistance eps (f.func '' U) = covering_number realDistance eps U ∧
    covering_number realDistance eps (g.func '' U) = covering_number realDistance eps U := by
  rw [images.1,images.2]
  exact ⟨rfl,rfl⟩

theorem differences {eps : ENNReal} (he : 0 < eps) (hef : eps < ⊤) :
    (∃ h : entropyDifferenceDefined realDistance realDistance f eps U,
      entropyDifference realDistance realDistance f eps U h = 0) ∧
    (∃ h : entropyDifferenceDefined realDistance realDistance g eps U,
      entropyDifference realDistance realDistance g eps U h = 0) := by
  have hne : U.Nonempty := ⟨some 0,by simp [U]⟩
  have hfin := finite_cover realDistance realDistance_metric.dist_self U (by simp [U]) he
  obtain ⟨r,hr⟩ := entropy_finite realDistance eps U hne hfin
  exact ⟨⟨⟨hne,domain.1,he,hef,Or.inl hfin⟩,by simp [entropyDifference,images.1,hr]⟩,
    ⟨⟨hne,domain.2,he,hef,Or.inl hfin⟩,by simp [entropyDifference,images.2,hr]⟩⟩

theorem bounds_at_seven_fourths :
    covering_number realDistance (7/4) (f.func '' U) = 2 ∧
    covering_number realDistance (7/4) (g.func '' U) = 2 ∧
    covering_number realDistance ((7/4)/1) U = 2 ∧
    covering_number realDistance ((7/4)/3) U = 4 ∧
    covering_number realDistance (7/4) (f.func '' U) ≤ covering_number realDistance ((7/4)/1) U ∧
    covering_number realDistance (7/4) (g.func '' U) ≤ covering_number realDistance ((7/4)/3) U := by
  have h1 : covering_number realDistance (7/4) U = 2 := by
    rw [covers (ENNReal.div_pos (by norm_num) (by norm_num)) (by finiteness)]
    norm_num [ENNReal.div_le_iff]
  have h3 : covering_number realDistance ((7/4)/3) U = 4 := by
    rw [covers (ENNReal.div_pos (ne_of_gt (ENNReal.div_pos (by norm_num) (by norm_num)))
      (by norm_num)) (by finiteness)]
    norm_num [ENNReal.div_le_iff]
  refine ⟨by simpa [images.1] using h1,by simpa [images.2] using h1,
    by simpa using h1,h3,?_,?_⟩
  · exact scalar_cover_lip realDistance realDistance f.func U (by norm_num) (by norm_num) lip_constants.1.2
  · exact scalar_cover_lip realDistance realDistance g.func U (by norm_num) (by norm_num) lip_constants.2.1.2

end
end Chapter3.Rearrangement
