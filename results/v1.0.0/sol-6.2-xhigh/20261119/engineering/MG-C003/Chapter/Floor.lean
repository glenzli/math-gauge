import Chapter.Step

open formal_oet.vol_01.ch_01_foundations
open scoped ENNReal
namespace Chapter.FloorExample

noncomputable def f := liftRealMap (fun x => (⌊x⌋ : ℝ))
noncomputable def d : Unit → Option ℝ → Option ℝ → ℝ≥0∞ := fun _ => realDist

def D1 : Set (Option ℝ) := realSet (Set.Icc 0 (1/2))
def D2 : Set (Option ℝ) := realSet (Set.Icc (9/10) (11/10))
def D3 : Set (Option ℝ) := realSet ({0,2} : Set ℝ)
def D4 : Set (Option ℝ) := realSet (Set.Icc 0 2)

theorem domain (S : Set ℝ) : realSet S ⊆ dom f := realSet_domain _ _

theorem gauge (i : Unit) : ExtendedPseudoMetric _ none (d i) := read_legal id

theorem floor_zero {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) : ⌊x⌋ = 0 :=
  Int.floor_eq_iff.mpr (by simpa using And.intro hx hx')

theorem one_value : f.func (some 1) = some 1 := by simp [f]

theorem zero_value : f.func (some 0) = some 0 := by simp [f]

theorem two_value : f.func (some 2) = some 2 := by simp [f]

noncomputable def kind (D : Set (Option ℝ)) (hn : D.Nonempty) : Bool × Bool :=
  thresholdType (diameterScale d) d f D hn 1 1 () ()

theorem kind_iff (D : Set (Option ℝ)) (hn : D.Nonempty) :
    kind D hn = (decide (diameter realDist D < 1),
      decide (1 ≤ uniform f realDist realDist D D)) := rfl

theorem interval_diameter (a b : ℝ) (hab : a ≤ b) :
    diameter realDist (realSet (Set.Icc a b)) = ENNReal.ofReal (b-a) :=
  realSet_diameter a b hab ⟨le_rfl,hab⟩ ⟨hab,le_rfl⟩ (fun _ h => h)

theorem at_boundary_zero {D : Set (Option ℝ)} (hD : D ⊆ dom f)
    (h1 : some (1 : ℝ) ∈ D)
    (hleft : ∀ a : ℝ, 0 < a → a ≤ 1/10 → some (1-a) ∈ D) :
    uniform f realDist realDist D D = 0 := by
  apply nonpos_iff_eq_zero.mp
  by_contra! h
  obtain ⟨r,hr,hr'⟩ := exists_between h
  have ht : r < ⊤ := hr'.trans_le le_top
  have hpos : 0 < r.toReal := ENNReal.toReal_pos hr.ne' ht.ne
  let a := min (r.toReal/2) (1/10)
  have ha : 0 < a := lt_min (by linarith) (by norm_num)
  have ha1 : a ≤ 1/10 := min_le_right _ _
  have har : a ≤ r.toReal/2 := min_le_left _ _
  have hx := hleft a ha ha1
  have hm : realDist (some (1-a)) (some 1) < r := by
    rw [real_some, ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg _) ht.ne,
      show 1-a-1 = -a by ring, abs_neg, abs_of_pos ha]
    linarith
  have he := uniform_zero hD ⟨_,h1⟩ hx h1 (hm.trans hr')
  have hf : f.func (some (1-a)) = some 0 := by
    simp [f, floor_zero (show 0 ≤ 1-a by linarith) (show 1-a < 1 by linarith)]
  rw [hf, one_value, real_zero] at he
  norm_num at he

theorem first :
    ∃ hn : D1.Nonempty, D1 ⊆ dom f ∧ diameter realDist D1 = ENNReal.ofReal (1/2) ∧
      uniform f realDist realDist D1 D1 = ⊤ ∧ kind D1 hn = (true,true) := by
  have hD : D1 ⊆ dom f := domain _
  have hd : diameter realDist D1 = ENNReal.ofReal (1/2) := by
    unfold D1
    rw [interval_diameter _ _ (by norm_num)]
    simp
  have he : ∀ x ∈ D1, f.func x = some 0 := by
    rintro _ ⟨a,ha,rfl⟩
    have h : a ∈ Set.Icc (0 : ℝ) (1/2) := ha
    simp [f, floor_zero h.1 (h.2.trans_lt (by norm_num))]
  have hu : uniform f realDist realDist D1 D1 = ⊤ := by
    apply top_unique
    exact le_uniform_iff.mpr fun y hy x hx _ => by simp [he x hx, he y hy]
  refine ⟨⟨some 0,by simp [D1]⟩,hD,hd,hu,?_⟩
  rw [kind_iff, hd, hu]
  norm_num [ENNReal.ofReal_lt_one]

theorem second :
    ∃ hn : D2.Nonempty, D2 ⊆ dom f ∧ diameter realDist D2 = ENNReal.ofReal (1/5) ∧
      uniform f realDist realDist D2 D2 = 0 ∧ kind D2 hn = (true,false) := by
  have hD : D2 ⊆ dom f := domain _
  have h1 : some (1 : ℝ) ∈ D2 := by norm_num [D2]
  have hd : diameter realDist D2 = ENNReal.ofReal (1/5) := by
    unfold D2
    rw [interval_diameter _ _ (by norm_num)]
    norm_num
  have hu := at_boundary_zero hD h1 (fun a ha ha1 => by
    rw [D2, mem_realSet]
    exact ⟨by linarith,by linarith⟩)
  refine ⟨⟨_,h1⟩,hD,hd,hu,?_⟩
  rw [kind_iff, hd, hu]
  norm_num [ENNReal.ofReal_lt_one]

theorem third :
    ∃ hn : D3.Nonempty, D3 ⊆ dom f ∧ diameter realDist D3 = 2 ∧
      uniform f realDist realDist D3 D3 = 2 ∧ kind D3 hn = (false,true) := by
  have hD : D3 ⊆ dom f := domain _
  have h0 : some (0 : ℝ) ∈ D3 := by simp [D3]
  have h2 : some (2 : ℝ) ∈ D3 := by simp [D3]
  have hd : diameter realDist D3 = 2 := by
    unfold D3
    rw [realSet_diameter 0 2 (by norm_num) (by simp) (by simp) (by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl <;> exact ⟨by norm_num,by norm_num⟩)]
    norm_num
  have hm : realDist (some 2) (some 0) = 2 := by norm_num
  have hm' : realDist (some 0) (some 2) = 2 := by norm_num
  have hn : D3.Nonempty := ⟨_,h0⟩
  have hu : uniform f realDist realDist D3 D3 = 2 := by
    apply le_antisymm
    · rw [← hm]
      apply uniform_separation hD hn h2 h0
      rw [two_value, zero_value, hm]
      norm_num
    · apply le_uniform_iff.mpr
      rintro _ ⟨y,hy,rfl⟩ _ ⟨x,hx,rfl⟩ h
      change y ∈ ({0,2} : Set ℝ) at hy
      change x ∈ ({0,2} : Set ℝ) at hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy hx
      rcases hy with rfl | rfl <;> rcases hx with rfl | rfl
      · exact (gauge ()).dist_self _
      · rw [hm] at h; exact (lt_irrefl _ h).elim
      · rw [hm'] at h; exact (lt_irrefl _ h).elim
      · exact (gauge ()).dist_self _
  refine ⟨hn,hD,hd,hu,?_⟩
  rw [kind_iff,hd,hu]
  norm_num

theorem fourth :
    ∃ hn : D4.Nonempty, D4 ⊆ dom f ∧ diameter realDist D4 = 2 ∧
      uniform f realDist realDist D4 D4 = 0 ∧ kind D4 hn = (false,false) := by
  have hD : D4 ⊆ dom f := domain _
  have h1 : some (1 : ℝ) ∈ D4 := by norm_num [D4]
  have hd : diameter realDist D4 = 2 := by
    unfold D4
    rw [interval_diameter _ _ (by norm_num)]
    norm_num
  have hu := at_boundary_zero hD h1 (fun a ha ha1 => by
    rw [D4, mem_realSet]
    exact ⟨by linarith,by linarith⟩)
  refine ⟨⟨_,h1⟩, hD, hd, hu, ?_⟩
  rw [kind_iff,hd,hu]
  norm_num

theorem large_without_collapse :
    D3.Nonempty ∧ D3 ⊆ dom f ∧ 1 ≤ uniform f realDist realDist D3 D3 ∧
      ∃ x ∈ D3, ∃ y ∈ D3, 0 < realDist (f.func x) (f.func y) := by
  obtain ⟨hn,hD,_,hu,_⟩ := third
  refine ⟨hn,hD,by rw [hu]; norm_num,some 0,by simp [D3],some 2,by simp [D3],?_⟩
  rw [zero_value,two_value]
  norm_num

end Chapter.FloorExample
