import FiniteExamples
open formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
open Set
namespace C3
noncomputable section
open scoped Classical
variable {X I : Type} {b : X}

namespace Rearrange
def U : Set (Option ℝ) := {pt 0,pt 1,pt 2,pt 3}
def perm (x : Option ℝ) := if x = pt 1 then pt 3 else if x = pt 2 then pt 1 else
  if x = pt 3 then pt 2 else pt 0
def restrictOp (v : Option ℝ → Option ℝ) : Op (none : Option ℝ) :=
  ⟨fun x => if x ∈ U then v x else none,by simp [U,pt]⟩
def F := restrictOp id
def G := restrictOp perm
abbrev p := line id

theorem values :
    (∀ x ∈ U, F.func x = x) ∧ G.func (pt 0) = pt 0 ∧ G.func (pt 1) = pt 3 ∧
    G.func (pt 2) = pt 1 ∧ G.func (pt 3) = pt 2 ∧
    (∀ x ∉ U, F.func x = none ∧ G.func x = none) := by
  norm_num [F,G,restrictOp,U,perm,pt]
  grind

theorem images : dom F = U ∧ dom G = U ∧ F.func '' U = U ∧ G.func '' U = U := by
  obtain ⟨hf,h0,h1,h2,h3,hout⟩ := values
  have dm (H : Op (none : Option ℝ)) (h : ∀ x ∈ U, H.func x ≠ none)
      (ho : ∀ x ∉ U, H.func x = none) : dom H = U := by
    ext x
    change H.func x ≠ none ↔ _
    exact ⟨fun hh => by_contra fun hn => hh (ho x hn),h x⟩
  refine ⟨dm F ?_ (fun x hx => (hout x hx).1),dm G ?_ (fun x hx => (hout x hx).2),?_,?_⟩
  · simp [U,F,restrictOp,pt]
  · simp [U,h0,h1,h2,h3,pt]
  · simpa using (Set.EqOn.image_eq (show Set.EqOn F.func id U from hf))
  · rw [U]
    simp only [image_insert_eq,image_singleton,h0,h1,h2,h3]
    ext x
    simp only [mem_insert_iff,mem_singleton_iff]
    tauto

theorem cover (e : ENNReal) (he : PosFin e) :
    cov p e U = if e ≤ 1 then 4 else if e ≤ 2 then 2 else 1 := by
  by_cases h1 : e ≤ 1
  · rw [if_pos h1]
    let S : Finset (Option ℝ) := {pt 0,pt 1,pt 2,pt 3}
    have hs : (S : Set (Option ℝ)) = U := by simp [S,U]
    have hh : ∀ x ∈ S, ∀ y ∈ S, p x y < e → x = y := by
      have h2 : e ≤ 2 := h1.trans (by norm_num)
      have h3 : e ≤ 3 := h1.trans (by norm_num)
      norm_num [S,pt,not_lt_of_ge h1,not_lt_of_ge h2,not_lt_of_ge h3]
    rw [← hs,isolated_cover he.1 (fun x _ => (line_metric id).dist_self x) hh]
    norm_num [S,pt,Finset.card_insert_of_notMem]
  · rw [if_neg h1]
    have he1 := lt_of_not_ge h1
    by_cases h2 : e ≤ 2
    · rw [if_pos h2]
      have h3 : e ≤ 3 := h2.trans (by norm_num)
      apply center_two (a := pt 1) (b := pt 2) (by simp [U]) (by simp [U])
      · norm_num [U,pt,he1,he.1]
      · norm_num [U,pt,h2,h3]
    · rw [if_neg h2]
      have he2 := lt_of_not_ge h2
      apply center_one (c := pt 1) (by simp [U])
      norm_num [U,pt,he1,he2,he.1]

theorem midpoint : pt (3/2) ∉ U ∧ ∀ x ∈ U, p x (pt (3/2)) < 7/4 := by
  have h : ENNReal.ofReal (3/2) < (7/4 : ENNReal) := by
    have hh := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 7/4)).mpr (by norm_num : (3/2:ℝ) < 7/4)
    norm_num [ENNReal.ofReal_div_of_pos] at hh ⊢
    exact hh
  have h' : ENNReal.ofReal (1/2) < (7/4 : ENNReal) :=
    (ENNReal.ofReal_le_ofReal (by norm_num : (1/2:ℝ) ≤ 3/2)).trans_lt h
  norm_num [U,pt,ENNReal.ofReal_div_of_pos] at *
  exact ⟨h,h',h⟩

theorem image_delta (e : ENNReal) (he : PosFin e) :
    ∀ H ∈ ({F,G} : Set (Op (none : Option ℝ))), H.func '' U = U ∧
    cov p e (H.func '' U) = cov p e U ∧ ∃ hw, delta p p H.func U e hw = 0 := by
  have hu : U.Nonempty := ⟨pt 0,by simp [U]⟩
  have finite : cov p e U < ⊤ := finite_cover (line_metric id).dist_self
    (by simp [U]) he.1
  obtain ⟨a,ha⟩ := finite_entropy hu finite
  intro H hH
  have hI : H.func '' U = U := by
    rcases (show H = F ∨ H = G from hH) with rfl | rfl
    · exact images.2.2.1
    · exact images.2.2.2
  exact ⟨hI,by rw [hI],Or.inl finite,by rw [delta,hI,ha,← EReal.coe_sub,sub_self,EReal.coe_zero]⟩

def Lip (H : Op (none : Option ℝ)) (L : ENNReal) :=
  ∀ x ∈ U, ∀ y ∈ U, p (H.func x) (H.func y) ≤ L * p x y

theorem optimal : IsLeast {L | Lip F L} 1 ∧ IsLeast {L | Lip G L} 3 := by
  obtain ⟨hf,h0,h1,h2,h3,_⟩ := values
  have hu0 : pt 0 ∈ U := by simp [U]
  have hu1 : pt 1 ∈ U := by simp [U]
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro x hx y hy
    simp [hf x hx,hf y hy]
  · intro L hL
    have hh := hL _ hu0 _ hu1
    simpa [hf _ hu0,hf _ hu1,pt] using hh
  · change Lip G 3
    norm_num [Lip,U,h0,h1,h2,h3,pt]
  · intro L hL
    have hh := hL _ hu0 _ hu1
    simpa [h0,h1,pt] using hh

theorem bounds :
    cov p (7/4) (F.func '' U) ≤ cov p ((7/4)/1) U ∧
    cov p (7/4) (G.func '' U) ≤ cov p ((7/4)/3) U ∧
    cov p (7/4) (F.func '' U) = 2 ∧ cov p ((7/4)/1) U = 2 ∧
    cov p (7/4) (G.func '' U) = 2 ∧ cov p ((7/4)/3) U = 4 := by
  have h₁ : PosFin 1 := ⟨by norm_num,by norm_num⟩
  have h₃ : PosFin 3 := ⟨by norm_num,by norm_num⟩
  have he : PosFin (7/4) := div_pf ⟨by norm_num,by norm_num⟩ ⟨by norm_num,by norm_num⟩
  have ha : (1:ENNReal) < 7/4 := (scaled_lt ⟨by norm_num,by norm_num⟩).mpr (by norm_num)
  have hb : (7/4:ENNReal) ≤ 2 := (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr (by norm_num)
  have hc : (7/4:ENNReal)/3 ≤ 1 := (ENNReal.div_le_iff h₃.1.ne' h₃.2.ne).mpr
    (by simpa using hb.trans (by norm_num : (2:ENNReal) ≤ 3))
  refine ⟨lip_cover optimal.1.1 h₁,lip_cover optimal.2.1 h₃,?_⟩
  simp [images.2.2.1,images.2.2.2,cover _ he,cover _ (div_pf he h₃),ha.not_ge,hb,hc]
end Rearrange

end
end C3
