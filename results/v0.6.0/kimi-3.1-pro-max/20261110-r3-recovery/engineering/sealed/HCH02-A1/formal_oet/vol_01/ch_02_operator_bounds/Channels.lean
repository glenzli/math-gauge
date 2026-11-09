import formal_oet.vol_01.ch_02_operator_bounds.Chains

namespace formal_oet.vol_01.ch_02_operator_bounds

open scoped BigOperators ENNReal Classical
open formal_oet.vol_01.ch_01_foundations

/-- HC02-P20.  The scalar feasible family is upward closed. -/
theorem scalarFeasible_upward {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    {lam₀ lam₁ : ENNReal}
    (h₀ : lam₀ ∈ scalarFeasible d ϕ U i j) (hle : lam₀ ≤ lam₁) :
    lam₁ ∈ scalarFeasible d ϕ U i j := by
  intro x hx y hy
  exact (h₀ x hx y hy).trans (mul_le_mul_right' hle _)

/-- Every constant strictly above the channel infimum is feasible. -/
theorem feasible_of_channelLip_lt {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    {lam : ENNReal} (h : channelLip d ϕ U i j < lam) :
    lam ∈ scalarFeasible d ϕ U i j := by
  obtain ⟨mu, hmu, hmulam⟩ := sInf_lt_iff.mp h
  exact scalarFeasible_upward d ϕ U i j hmu hmulam.le

/-- HC02-P21.  The above-infimum feasibility statement in the positive
finite context of the text. -/
theorem feasible_above_positive_finite_channelLip {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (_ha : 0 < channelLip d ϕ U i j) (_hfin : channelLip d ϕ U i j < ∞)
    {lam : ENNReal} (h : channelLip d ϕ U i j < lam) :
    lam ∈ scalarFeasible d ϕ U i j := by
  exact feasible_of_channelLip_lt d ϕ U i j h

/-- HC02-P22.  If the infimum is zero, every finite strictly positive
constant is feasible. -/
theorem feasible_of_channelLip_eq_zero {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ha : channelLip d ϕ U i j = 0) {lam : ENNReal}
    (hpos : 0 < lam) (_hfin : lam < ∞) :
    lam ∈ scalarFeasible d ϕ U i j := by
  apply feasible_of_channelLip_lt d ϕ U i j
  rwa [ha]

/-- HC02-P18.  A zero input distance with positive output distance rules out
every extended scalar constant. -/
theorem scalarFeasible_eq_empty_of_zero_input_positive_output {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (ϕ.func x) (ϕ.func y)) :
    scalarFeasible d ϕ U i j = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro lam hlam
  have hbound := hlam x hx y hy
  rw [hin, mul_zero] at hbound
  exact (not_le_of_gt hout) hbound

/-- HC02-P18.  Consequently, the single-channel infimum is `+∞`. -/
theorem channelLip_eq_top_of_zero_input_positive_output {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (x y : X) (hx : x ∈ U) (hy : y ∈ U)
    (hin : d i x y = 0) (hout : 0 < d j (ϕ.func x) (ϕ.func y)) :
    channelLip d ϕ U i j = ∞ := by
  rw [channelLip, scalarFeasible_eq_empty_of_zero_input_positive_output
    d ϕ U i j x y hx hy hin hout]
  exact sInf_empty

/-- HC02-P19.  A positive finite optimal single-channel constant is itself
feasible. -/
theorem channelLip_mem_of_pos_finite {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I)
    (ha : 0 < channelLip d ϕ U i j) (hfin : channelLip d ϕ U i j < ∞) :
    channelLip d ϕ U i j ∈ scalarFeasible d ϕ U i j := by
  intro x hx y hy
  by_cases hBzero : d i x y = 0
  · obtain ⟨lam, halam, hlamfin⟩ := exists_between hfin
    have hbound := (feasible_of_channelLip_lt d ϕ U i j halam) x hx y hy
    rw [hBzero, mul_zero] at hbound
    have hAzero : d j (ϕ.func x) (ϕ.func y) = 0 := le_antisymm hbound (zero_le _)
    simp [hBzero, hAzero]
  by_cases hBtop : d i x y = ∞
  · rw [hBtop, ENNReal.mul_top ha.ne']
    exact le_top
  · have hBpos : 0 < d i x y := pos_iff_ne_zero.mpr hBzero
    by_contra hnot
    have hlt : channelLip d ϕ U i j * d i x y < d j (ϕ.func x) (ϕ.func y) :=
      lt_of_not_ge hnot
    have hadiv : channelLip d ϕ U i j < d j (ϕ.func x) (ϕ.func y) / d i x y :=
      (ENNReal.lt_div_iff_mul_lt (Or.inl hBzero) (Or.inl hBtop)).mpr hlt
    obtain ⟨lam, halam, hlamdiv⟩ := exists_between hadiv
    have hbound := (feasible_of_channelLip_lt d ϕ U i j halam) x hx y hy
    have hlamlt : lam * d i x y < d j (ϕ.func x) (ϕ.func y) :=
      ENNReal.mul_lt_of_lt_div hlamdiv
    exact (not_lt_of_ge hbound) hlamlt

/-- HC02-P24.  Finiteness of the channel infimum is equivalent to existence
of one finite feasible constant. -/
theorem channelLip_lt_top_iff_exists_finite {X I : Type} {bot : X}
    (d : I → X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) (i j : I) :
    channelLip d ϕ U i j < ∞ ↔
      ∃ lam : ENNReal, lam < ∞ ∧ lam ∈ scalarFeasible d ϕ U i j := by
  constructor
  · intro h
    obtain ⟨lam, hlam, hlamtop⟩ := sInf_lt_iff.mp h
    exact ⟨lam, hlamtop, hlam⟩
  · rintro ⟨lam, hlamtop, hlam⟩
    exact (sInf_le hlam).trans_lt hlamtop

/-! ### The zero-infimum counterexample -/

/-- HC02-P23.  Two nonabsorbing points and one absorbing point. -/
abbrev CounterPoint := Option Bool

/-- The absorbing point of the counterexample. -/
def counterBot : CounterPoint := none

/-- Distinct points are at infinite extended distance. -/
def counterDist : CounterPoint → CounterPoint → ENNReal :=
  fun x y => if x = y then 0 else ∞

/-- HC02-P23.  This is a legal extended pseudometric with the required
absorbing-point isolation. -/
theorem counterDist_extendedPseudoMetric :
    ExtendedPseudoMetric CounterPoint counterBot counterDist := by
  refine
    { nonabsorbing := ⟨some false, by simp [counterBot]⟩
      dist_self := ?_
      symm := ?_
      triangle := ?_
      isolate_bot := ?_ }
  · intro x
    simp [counterDist]
  · intro x y
    fin_cases x <;> fin_cases y <;> simp [counterDist]
  · intro x y z
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [counterDist]
  · intro x hx
    fin_cases x <;> simp_all [counterDist, counterBot]

/-- The identity operator on the counterexample space. -/
def counterOperator : Operator CounterPoint counterBot := ⟨id, rfl⟩

/-- A nonempty legal evaluation domain containing both nonabsorbing points. -/
def counterU : Set CounterPoint := {some false, some true}

theorem counterU_nonempty : counterU.Nonempty := by
  exact ⟨some false, by simp [counterU]⟩

theorem counterU_subset_dom : counterU ⊆ dom counterOperator := by
  intro x hx
  rcases (by simpa [counterU] using hx : x = some false ∨ x = some true) with rfl | rfl <;>
    simp [dom, counterOperator, counterBot]

/-- HC02-P23.  For the distinguished channel, the feasible scalars are
exactly the nonzero extended nonnegative reals. -/
theorem counter_scalarFeasible (lam : ENNReal) :
    lam ∈ scalarFeasible (fun _ : Unit => counterDist) counterOperator counterU () () ↔
      lam ≠ 0 := by
  constructor
  · intro hlam
    intro hzero
    subst lam
    have hbound := hlam (some false) (by simp [counterU])
      (some true) (by simp [counterU])
    simp [counterOperator, counterDist] at hbound
  · intro hne x hx y hy
    have hx' : x = some false ∨ x = some true := by simpa [counterU] using hx
    have hy' : y = some false ∨ y = some true := by simpa [counterU] using hy
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl <;>
      simp [counterOperator, counterDist, hne]

/-- The feasible set is precisely `(0, +∞]` in `ENNReal`. -/
theorem counter_scalarFeasible_set :
    scalarFeasible (fun _ : Unit => counterDist) counterOperator counterU () () = Set.Ioi 0 := by
  ext lam
  simp [counter_scalarFeasible, pos_iff_ne_zero]

/-- HC02-P23.  The channel infimum is zero, but zero is not feasible. -/
theorem counterexample_zero_infimum_not_attained :
    channelLip (fun _ : Unit => counterDist) counterOperator counterU () () = 0 ∧
      (0 : ENNReal) ∉ scalarFeasible (fun _ : Unit => counterDist)
        counterOperator counterU () () := by
  constructor
  · rw [channelLip, counter_scalarFeasible_set]
    apply sInf_eq_of_forall_ge_of_forall_gt_exists_lt
    · intro a ha
      exact zero_le a
    · intro w hw
      obtain ⟨a, ha, haw⟩ := exists_between hw
      exact ⟨a, ha, haw⟩
  · intro hzero
    exact (counter_scalarFeasible 0).mp hzero rfl

end formal_oet.vol_01.ch_02_operator_bounds
