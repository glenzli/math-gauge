import Ch3.Entropy

namespace MG
open Set formal_oet.vol_01.ch_01_foundations formal_oet.vol_01.ch_02_operator_bounds
noncomputable section
variable {X I : Type} {b : X} {d : I → Dist X} {f g : Op b} {U : Set X}
variable {p q : Dist X} {e : ENNReal}

def constSet (d : I → Dist X) (f : Op b) (U : Set X) := {i | Const (d i) f U}
def identSet (d : I → Dist X) (f : Op b) (U : Set X) := {i | Ident (d i) f U}
def activeSet (d : I → Dist X) (f : Op b) (U : Set X) := {i | Active (d i) f U}

theorem componentSets :
    identSet d f U = {i ∈ (constSet d f U)ᶜ | ∀ x ∈ U, d i (f.func x) x = 0} ∧
    activeSet d f U = (constSet d f U ∪ identSet d f U)ᶜ := by
  refine ⟨rfl,?_⟩
  ext i
  exact not_or.symm

theorem compSets (m : ∀ i, ExtendedPseudoMetric X b (d i)) (_hU : U ⊆ dom (g*f)) :
    activeSet d (g*f) U ⊆ activeSet d f U ∪ activeSet d g (f.func '' U) ∧
    identSet d f U ∩ identSet d g (f.func '' U) ⊆ identSet d (g*f) U :=
  ⟨fun i h => compActive (m i) h,fun i h => compIdent (m i) h.1 h.2⟩

def prefixOp (F : ℕ → Op b) : ℕ → Op b
  | 0 => 1
  | n+1 => F n * prefixOp F n

theorem prefixDomains (F : ℕ → Op b) (n : ℕ) :
    (prefixOp F 0).func '' U = U ∧
    (prefixOp F (n+1)).func '' U = (F n).func '' ((prefixOp F n).func '' U) := by
  exact ⟨Set.image_id U,by rw [Set.image_image]; rfl⟩

theorem finiteActive (m : ∀ i, ExtendedPseudoMetric X b (d i)) (F : ℕ → Op b) (n : ℕ)
    (hu : U ⊆ dom (prefixOp F n)) :
    (∀ k < n, (prefixOp F k).func '' U ⊆ dom (F k)) ∧
    activeSet d (prefixOp F n) U ⊆ ⋃ k < n, activeSet d (F k) ((prefixOp F k).func '' U) := by
  induction n with
  | zero =>
    exact ⟨fun k hk => (Nat.not_lt_zero k hk).elim,fun i hi => (emptyActive (m i) hi).elim⟩
  | succ n ih =>
    have hprev : U ⊆ dom (prefixOp F n) := by
      intro x hx hb
      apply hu hx
      change (F n).func ((prefixOp F n).func x) = b
      rw [hb,(F n).preserves_bot]
    obtain ⟨hd,ha⟩ := ih hprev
    constructor
    · intro k hk
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with h|rfl
      · exact hd k h
      · rintro _ ⟨x,hx,rfl⟩
        exact hu hx
    · intro i hi
      rcases compActive (m i) (f := prefixOp F n) (g := F n) hi with h|h
      · obtain ⟨k,hk,hi⟩ := Set.mem_iUnion₂.mp (ha h)
        exact Set.mem_iUnion₂.mpr ⟨k,by omega,hi⟩
      · exact Set.mem_iUnion₂.mpr ⟨n,Nat.lt_succ_self n,h⟩

theorem subdistMaximum [Finite I] {J : Set I} (hJ : J.Nonempty) (x y : X) :
    IsGreatest ((fun j => d j x y) '' J) (subdist d J x y) := by
  letI : Nonempty J := hJ.to_subtype
  obtain ⟨j,hj⟩ := exists_eq_ciSup_of_finite (f := fun k : J => d k x y)
  exact ⟨⟨j,j.2,hj⟩,fun _ ⟨i,hi,e⟩ => e ▸ le_iSup (fun k : J => d k x y) ⟨i,hi⟩⟩

theorem fiberEmpty {y : X} (h : ∀ z ∈ f.func '' U, 0 < p z y) : fiber p f U y = ∅ :=
  Set.eq_empty_iff_forall_notMem.2 fun _ hx => (h _ (mem_image_of_mem _ hx.1)).ne' hx.2

theorem blockPartition (m : ExtendedPseudoMetric X b p) :
    (∀ s ∈ blocks p f U, s.Nonempty) ∧ ⋃₀ (blocks p f U) = U ∧
      (blocks p f U).PairwiseDisjoint id := by
  obtain ⟨hn,hu⟩ := fiberCover (f := f) (U := U) m
  exact ⟨hn,hu,fun _ h _ k hne => (fiberPartition m h k).resolve_left hne⟩

theorem finerFibers (m : ∀ i, ExtendedPseudoMetric X b (d i)) :
    finer d U f g ↔ ∀ x ∈ U, fiber (subdist d univ) f U (f.func x) ⊆
      fiber (subdist d univ) g U (g.func x) := by
  constructor
  · intro h x hx y hy
    exact (relationFiber m hx hy.1).1 (h ((relationFiber m hx hy.1).2 hy))
  · intro h z hz
    exact (relationFiber m hz.1 hz.2.1).2 (h _ hz.1 ((relationFiber m hz.1 hz.2.1).1 hz))

theorem finiteFiner {n : ℕ} (F : Fin (n+1) → Op b) (_hd : ∀ k, U ⊆ dom (F k))
    (h : ∀ k : Fin n, finer d U (F k.castSucc) (F k.succ)) {a c : Fin (n+1)} (hac : a ≤ c) :
    finer d U (F a) (F c) :=
  ((Fin.monotone_iff_le_succ (f := fun i => zeroRel d (F i) U)).2 h) hac

theorem strictFiniteFiner {n : ℕ} (F : Fin (n+1) → Op b) (hd : ∀ k, U ⊆ dom (F k))
    (h : ∀ k : Fin n, finer d U (F k.castSucc) (F k.succ)) {k : Fin n}
    (hs : zeroRel d (F k.castSucc) U ⊂ zeroRel d (F k.succ) U) :
    zeroRel d (F 0) U ⊂ zeroRel d (F (Fin.last n)) U ∧
      ∃ z ∈ zeroRel d (F k.succ) U \ zeroRel d (F k.castSucc) U,
        z ∈ zeroRel d (F (Fin.last n)) U \ zeroRel d (F 0) U := by
  obtain ⟨z,hz,hn⟩ := Set.exists_of_ssubset hs
  have hz' := finiteFiner F hd h (Fin.le_last k.succ) hz
  have hn' : z ∉ zeroRel d (F 0) U := fun hc => hn (finiteFiner F hd h (Fin.zero_le _) hc)
  exact ⟨⟨finiteFiner F hd h (Fin.zero_le _),fun hc => hn' (hc hz')⟩,z,⟨hz,hn⟩,hz',hn'⟩

theorem pointMinimum [Finite I] {J : Set I} (hJ : J.Nonempty) (i : I) (y : X) :
    IsLeast ((fun j => radius (d i) (d j) f U y) '' J) (radius (d i) (subdist d J) f U y) := by
  rw [radiusInf]
  obtain ⟨j,hj,he⟩ := finiteMin hJ (fun k => radius (d i) (d k) f U y)
  exact ⟨⟨j,hj,he⟩,fun _ ⟨k,hk,e⟩ => e ▸ iInf_le (fun t : J => radius (d i) (d t) f U y) ⟨k,hk⟩⟩

theorem matrixMinimum [Finite I] {J : Set I} (hJ : J.Nonempty) (i : I) :
    IsLeast ((fun j => matrix d f U j i) '' J) (uniform (d i) (subdist d J) f U U) := by
  rw [uniformInf]
  obtain ⟨j,hj,he⟩ := finiteMin hJ (fun k => matrix d f U k i)
  exact ⟨⟨j,hj,he⟩,fun _ ⟨k,hk,e⟩ => e ▸ iInf_le (fun t : J => matrix d f U t i) ⟨k,hk⟩⟩

theorem radiusNotation {J : Set I} (i j : I) (y : X) :
    radius (d i) (subdist d {j}) f U y = radius (d i) (d j) f U y ∧
    (∀ A : Set X, uniform (d i) (subdist d J) f A U = ⨅ a : A, radius (d i) (subdist d J) f U a) ∧
    matrix d f U j i = ⨅ a : U, radius (d i) (d j) f U a := by
  rw [show subdist d {j} = d j from subfamily_pseudometric_singleton d j]
  exact ⟨rfl,fun _ => rfl,rfl⟩

theorem channelTable (σ : Scale X I) (A : Region X) (_hA : A.val ⊆ dom f)
    {s t : ENNReal} (_hs : positiveFinite s) (_ht : positiveFinite t) (i j : I) :
    let c := channel σ d f A s t (i,j)
    let a := σ.value i A
    let n := matrix d f A j i
    (c = (true,true) ↔ a < s ∧ t ≤ n) ∧ (c = (true,false) ↔ a < s ∧ n < t) ∧
    (c = (false,true) ↔ s ≤ a ∧ t ≤ n) ∧ (c = (false,false) ↔ s ≤ a ∧ n < t) := by
  simp [channel,bits]

theorem boundedNets : boundedAtAll p U ↔ ∀ r, positiveFinite r → ∃ C, Net p r U C := by
  simp only [boundedAtAll,lt_top_iff_ne_top,ne_eq,cover,covering_number_eq_top_iff,not_not,Net]

theorem entropyOrder {V : Set X} {r : ENNReal} :
    entropy p e U ≤ entropy q r V ↔ cover p e U ≤ cover q r V := logStrict.le_iff_le

theorem deltaSigns (hne : U.Nonempty) (h : good p q f U e) :
    (0 < delta p q f U e h ↔ entropy q e (f.func '' U) < entropy p e U) ∧
    (delta p q f U e h < 0 ↔ entropy p e U < entropy q e (f.func '' U)) ∧
    (delta p q f U e h = 0 ↔ entropy p e U = entropy q e (f.func '' U)) := by
  have ht : entropy p e U ≠ ⊤ ∨ entropy q e (f.func '' U) ≠ ⊤ := by
    rcases h with hi|ho
    · obtain ⟨a,ha⟩ := finiteLog hne hi
      exact Or.inl (ha ▸ EReal.coe_ne_top a)
    · obtain ⟨a,ha⟩ := finiteLog (hne.image _) ho
      exact Or.inr (ha ▸ EReal.coe_ne_top a)
  have hb : entropy p e U ≠ ⊥ := ((show (⊥ : EReal) < 0 by simp).trans_le (metric_entropy_nonneg _ _ _ hne)).ne'
  have neg := EReal.sub_neg ht (Or.inl hb)
  refine ⟨EReal.sub_pos,neg,?_⟩
  change _ - _ = 0 ↔ _
  constructor
  · intro he
    exact le_antisymm (le_of_not_gt fun k => (EReal.sub_pos.2 k).ne' he)
      (le_of_not_gt fun k => (neg.2 k).ne he)
  · intro he
    exact le_antisymm (EReal.sub_nonpos.2 he.le) (le_of_not_gt fun k => (neg.1 k).ne he)

theorem lipCenters {L : ENNReal} (hl : positiveFinite L)
    (h : ∀ x ∈ U, ∀ y ∈ U, q (f.func x) (f.func y) ≤ L*p x y)
    (C : Finset X) (hc : Net p (e/L) U C) :
    ∃ T : Finset X, Net q e (f.func '' U) T ∧ T.card ≤ C.card :=
  pushNet hc fun x hx y hy hd => (h _ hx _ hy).trans_lt
    (by simpa [mul_comm] using (ENNReal.lt_div_iff_mul_lt (Or.inl hl.1.ne') (Or.inl hl.2.ne)).1 hd)

theorem coCenters [Fintype I] (K : I → I → ENNReal) (i j : I)
    (hK : IsCoLipMatrix d f U K) (hk : positiveFinite (K i j))
    (T : Finset X) (ht : Net (d j) e (f.func '' U) T) :
    ∃ C : Finset X, Net (d i) (e/K i j) U C ∧ C.card ≤ T.card := by
  apply pullNet ht
  intro x hx y hy hd
  apply (ENNReal.lt_div_iff_mul_lt (Or.inl hk.1.ne') (Or.inl hk.2.ne)).2
  rw [mul_comm]
  exact (Finset.single_le_sum (f := fun k => K k j * d k x y) (fun _ _ => zero_le _) (Finset.mem_univ i)).trans_lt
    ((hK.2.2 x hx y hy j).trans_lt hd)

end
end MG
