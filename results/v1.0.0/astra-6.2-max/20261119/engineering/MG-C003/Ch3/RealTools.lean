import Ch3.Models
import Ch3.Entropy

namespace MG
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
variable {X : Type} {b : X} {p q : Dist X} {f : Op b} {A : Set X} {e : ENNReal}

theorem twoLower (hne : A.Nonempty) (hn : ∀ c ∈ A, ∃ x ∈ A, e ≤ p x c) :
    2 ≤ cover p e A := by
  classical
  apply coverLower
  intro C hC
  suffices 2 ≤ C.card by exact_mod_cast this
  by_contra! hc
  obtain ⟨a,ha⟩ := hne
  obtain ⟨c,hc',_⟩ := hC.2 a ha
  obtain ⟨x,hx,hbad⟩ := hn c (hC.1 hc')
  obtain ⟨z,hz,hd⟩ := hC.2 x hx
  have heq := Finset.card_le_one.mp (show C.card ≤ 1 by omega) z hz c hc'
  exact hbad.not_gt (heq ▸ hd)

theorem fullSeparated (S : Finset X) (m : ExtendedPseudoMetric X b p) (he : 0 < e)
    (hs : ∀ x ∈ S, ∀ y ∈ S, p x y < e → x = y) : cover p e (S : Set X) = S.card := by
  apply le_antisymm
  · exact netUpper ⟨Subset.rfl,fun x hx => ⟨x,hx,(m.dist_self _).trans_lt he⟩⟩
  · apply coverLower
    intro C hC
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro x hx
    obtain ⟨y,hy,hd⟩ := hC.2 x hx
    exact hs x hx y (hC.1 hy) hd ▸ hy

theorem pairCover (m : ExtendedPseudoMetric X b p) (a c : X) (he : 0 < e) :
    cover p e {a,c} = if p a c < e then 1 else 2 := by
  classical
  have ha : a ∈ ({a,c} : Set X) := Or.inl rfl
  have hc : c ∈ ({a,c} : Set X) := Or.inr rfl
  split_ifs with h
  · apply coverOne ⟨a,ha⟩ hc
    intro x hx
    rcases hx with h'|h' <;> rw [h']
    · exact h
    · simpa [m.dist_self] using he
  · have hne : a ≠ c := fun heq => h (heq ▸ (m.dist_self c).trans_lt he)
    let S : Finset X := {a,c}
    have hS : (S : Set X) = {a,c} := by simp [S]
    rw [← hS,fullSeparated S m he]
    · simp [S,hne]
    · intro x hx y hy hd
      have hx' : x ∈ ({a,c} : Set X) := hS ▸ hx
      have hy' : y ∈ ({a,c} : Set X) := hS ▸ hy
      change x = a ∨ x = c at hx'
      change y = a ∨ y = c at hy'
      rcases hx' with h₁|h₁ <;> rcases hy' with h₂|h₂ <;> simp only [h₁,h₂] at hd ⊢
      all_goals first | rfl | exact (h hd).elim | exact (h ((m.symm a c).trans_lt hd)).elim

theorem smallZero {v : ENNReal} (h : ∀ t : ℝ, 0 < t → v ≤ ENNReal.ofReal t) : v = 0 := by
  by_contra hn
  obtain ⟨r,hp,hr⟩ := exists_between (pos_iff_ne_zero.2 hn)
  have hf := (hr.trans_le le_top).ne
  have H := h r.toReal (ENNReal.toReal_pos hp.ne' hf)
  rw [ENNReal.ofReal_toReal hf] at H
  exact hr.not_ge H

theorem realDiam {S : Set ℝ} {u v : ℝ} (hu : u ∈ S) (hv : v ∈ S) (h : S ⊆ Icc u v) :
    diam usual (realSet S) = ENNReal.ofReal (v-u) := by
  apply le_antisymm
  · apply diam_le
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
    simp only [usual,read_points,id_eq]
    apply ENNReal.ofReal_le_ofReal
    exact abs_le.mpr ⟨by linarith [(h hx).1,(h hy).2],by linarith [(h hx).2,(h hy).1]⟩
  · have H := le_diam (p := usual) (mem_realSet.mpr hv) (mem_realSet.mpr hu)
    simpa [usual,abs_of_nonneg (sub_nonneg.mpr (h hv).1)] using H

theorem intervalDiam {u v : ℝ} (huv : u ≤ v) :
    diam usual (realSet (Icc u v)) = ENNReal.ofReal (v-u) :=
  realDiam ⟨le_rfl,huv⟩ ⟨huv,le_rfl⟩ Subset.rfl

theorem pairDiam {u v : ℝ} (huv : u ≤ v) :
    diam usual (realSet {u,v}) = ENNReal.ofReal (v-u) := by
  apply realDiam (Or.inl rfl) (Or.inr rfl)
  rintro _ (rfl|h)
  · exact ⟨le_rfl,huv⟩
  · rw [Set.mem_singleton_iff.mp h]
    exact ⟨huv,le_rfl⟩

theorem scaleCounter :
    let A := realSet {0,1}
    let B := realSet {0}
    B.Nonempty ∧ B ⊆ A ∧ A ⊆ dom (1 : Op (none : Line)) ∧
    diam usual B = 0 ∧ diam usual A = 1 ∧
    diam usual B < (1/2 : ENNReal) ∧ (1/2 : ENNReal) ≤ diam usual A := by
  dsimp only
  have ha : diam usual (realSet {0,1}) = 1 := by norm_num [pairDiam (u := 0) (v := 1) (by norm_num)]
  have hb := pairDiam (u := 0) (v := 0) le_rfl
  simp at hb
  refine ⟨⟨pt 0,mem_realSet.2 rfl⟩,Set.image_mono (by simp),?_,hb,ha,?_,?_⟩
  · rintro _ ⟨x,_,rfl⟩
    exact Option.some_ne_none _
  · rw [hb]; norm_num
  · rw [ha]; norm_num

end
end MG
