import Ch3.Radius

namespace MG
open Set formal_oet.vol_01.ch_01_foundations
noncomputable section
variable {X I : Type} {b : X} {f : Op b} {U A B : Set X} {p q : Dist X}
def diam (p : Dist X) (A : Set X) := ⨆ x : A, ⨆ y : A, p x y
theorem le_diam {x y : X} (hx : x ∈ A) (hy : y ∈ A) : p x y ≤ diam p A :=
  le_iSup_of_le (⟨x,hx⟩ : A) (le_iSup_of_le (⟨y,hy⟩ : A) le_rfl)
theorem diam_le {t : ENNReal} (h : ∀ x ∈ A, ∀ y ∈ A, p x y ≤ t) : diam p A ≤ t :=
  iSup_le fun x => iSup_le fun y => h _ x.2 _ y.2

abbrev Region (X : Type) := {A : Set X // A.Nonempty}
structure Scale (X I : Type) where
  value : I → Region X → ENNReal
  mono : ∀ i A B, A.val ⊆ B.val → value i A ≤ value i B

def diamScale (d : I → Dist X) : Scale X I :=
  ⟨fun i A => diam (d i) A,fun _ _ _ h => diam_le fun _ hx _ hy => le_diam (h hx) (h hy)⟩

def bits (a n ts tn : ENNReal) : Bool × Bool := (decide (a < ts), decide (tn ≤ n))
def channel (σ : Scale X I) (d : I → Dist X) (f : Op b) (A : Region X)
    (ts tn : ENNReal) (ij : I × I) := bits (σ.value ij.1 A) (matrix d f A.val ij.2 ij.1) ts tn

theorem fourTypes (a n ts tn : ENNReal) :
    ∃! z : Bool × Bool,
      (z = (true,true) ∧ a < ts ∧ tn ≤ n) ∨ (z = (true,false) ∧ a < ts ∧ n < tn) ∨
      (z = (false,true) ∧ ts ≤ a ∧ tn ≤ n) ∨ (z = (false,false) ∧ ts ≤ a ∧ n < tn) := by
  refine ⟨bits a n ts tn, ?_, ?_⟩
  all_goals by_cases h : a < ts <;> by_cases k : tn ≤ n <;>
    simp_all [bits, not_lt, not_le, not_lt_of_ge, not_le_of_gt]

theorem scaleChannels (σ : Scale X I) (d : I → Dist X) (f : Op b) (A : Region X)
    {s s' t : ENNReal} (hs : s ≤ s') :
    {ij | (channel σ d f A s t ij).1 = true} ⊆ {ij | (channel σ d f A s' t ij).1 = true} := by
  intro ij
  simp only [mem_setOf_eq,channel,bits,decide_eq_true_eq]
  exact fun h => h.trans_le hs

theorem radiusChannels (σ : Scale X I) (d : I → Dist X) (f : Op b) (A : Region X)
    {s t t' : ENNReal} (ht : t ≤ t') :
    {ij | (channel σ d f A s t' ij).2 = true} ⊆ {ij | (channel σ d f A s t ij).2 = true} := by
  intro ij
  simp only [mem_setOf_eq,channel,bits,decide_eq_true_eq]
  exact fun h => ht.trans h

theorem scaleRestrict (σ : Scale X I) (i : I) (A B : Region X) (h : B.val ⊆ A.val) (ts : ENNReal) :
    σ.value i B ≤ σ.value i A ∧ (σ.value i A < ts → σ.value i B < ts) :=
  ⟨σ.mono i B A h,fun ht => (σ.mono i B A h).trans_lt ht⟩

theorem smallDomain {ts tn : ENNReal} (hs : diam p A < ts) (ht : ts ≤ tn) :
    tn ≤ uniform p q f A A ↔ Const q f A :=
  ⟨fun hr _ hx _ hy => cutUniform hx hy ((le_diam hx hy).trans_lt (hs.trans_le (ht.trans hr))),
    fun hc => (constRadii p hc).2 ▸ le_top⟩

end
end MG
