import Counterexample

noncomputable section
open scoped BigOperators ENNReal NNReal
open Filter Topology
namespace MathGauge.RecursiveClosure.Counterexample

def actualInputEquiv : ℤ ≃ Set.range inputEmbedding :=
  Equiv.ofInjective inputEmbedding inputEmbedding_injective

theorem metric_matches_gauge (x y : Y) :
    edist x y = max (gauge.d 0 x y) (gauge.d 1 x y) := by
  simp [edist_dist,Prod.dist_eq,Real.dist_eq,gauge,coordinate]

theorem tendsto_from_even_odd {Z : Type} [TopologicalSpace Z] (f : ℕ → Z) (z : Z)
    (he : Tendsto (fun k => f (2*k)) atTop (𝓝 z))
    (ho : Tendsto (fun k => f (2*k+1)) atTop (𝓝 z)) : Tendsto f atTop (𝓝 z) := by
  rw [Filter.tendsto_def] at *
  intro S hS
  obtain ⟨Ne,hNe⟩ := eventually_atTop.1 (he S hS)
  obtain ⟨No,hNo⟩ := eventually_atTop.1 (ho S hS)
  apply eventually_atTop.2
  refine ⟨2*(max Ne No)+1,?_⟩
  intro n hn
  rcases Nat.even_or_odd n with ⟨k,hk⟩|⟨k,hk⟩
  · have hkN : Ne ≤ k := by omega
    have hn' : n=2*k := by omega
    simpa [hn'] using hNe k hkN
  · have hkN : No ≤ k := by omega
    have hn' : n=2*k+1 := by omega
    simpa [hn'] using hNo k hkN

theorem polynomial_geometric_limit (a : ℝ) :
    Tendsto (fun k : ℕ => (a+(k:ℝ))/4^k) atTop (𝓝 0) := by
  have hp : Tendsto (fun k : ℕ => (1/4:ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
  have hk := tendsto_self_mul_const_pow_of_lt_one (r := (1/4:ℝ)) (by norm_num) (by norm_num)
  have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => a) atTop (𝓝 a)).mul hp).add hk
  simpa [div_eq_mul_inv,inv_pow,add_mul] using hh

theorem even_second_zero (k : ℕ) (n : ℤ) (hn : 0<n) :
    sys.transform^[2*(k+1)] initial true n = (0,0) := by
  rw [show 2*(k+1)=(2*k+1)+1 by omega,Function.iterate_succ_apply']
  rw [(unfold_one _ n hn).2]
  rw [(unfold_formulas k (n+1) (by omega)).2.2]
  norm_num [ret]

theorem pointwise_unfold_limit (v : Bool) (n : ℤ) :
    Tendsto (fun k : ℕ => sys.transform^[k] initial v n) atTop (𝓝 ((0,0):Y)) := by
  by_cases hn : n≤0
  · have he : (fun k : ℕ => sys.transform^[k] initial v n) =ᶠ[atTop] fun _ => ((0,0):Y) := by
      apply eventually_atTop.2
      refine ⟨1,?_⟩
      intro k hk
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
      exact sys.iterate_stop initial (by simp [sys,hn]) j
    exact (Filter.tendsto_congr' he).2 tendsto_const_nhds
  · have hn' : 0<n := by omega
    apply tendsto_from_even_odd
    · cases v with
      | false =>
        have he : (fun k : ℕ => sys.transform^[2*k] initial false n) =
            (fun k : ℕ => (((n:ℝ)+(k:ℝ))/4^k,0)) :=
          funext fun k => (unfold_formulas k n hn').1
        rw [he]
        exact (polynomial_geometric_limit n).prodMk_nhds tendsto_const_nhds
      | true =>
        have he : (fun k : ℕ => sys.transform^[2*k] initial true n) =ᶠ[atTop] fun _ => ((0,0):Y) := by
          apply eventually_atTop.2
          refine ⟨1,?_⟩
          intro k hk
          obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
          exact even_second_zero j n hn'
        exact (Filter.tendsto_congr' he).2 tendsto_const_nhds
    · cases v with
      | false =>
        have he : (fun k : ℕ => sys.transform^[2*k+1] initial false n) = fun _ => ((0,0):Y) :=
          funext fun k => (unfold_formulas k n hn').2.2
        rw [he]
        exact tendsto_const_nhds
      | true =>
        have he : (fun k : ℕ => sys.transform^[2*k+1] initial true n) =
            (fun k : ℕ => (0,((n:ℝ)+(k:ℝ)+1)/(2*4^k))) :=
          funext fun k => (unfold_formulas k n hn').2.1
        rw [he]
        have hp := (polynomial_geometric_limit ((n:ℝ)+1)).div_const 2
        have hlim : Tendsto (fun k : ℕ => ((n:ℝ)+(k:ℝ)+1)/(2*4^k)) atTop (𝓝 0) := by
          simpa [div_eq_mul_inv,mul_inv_rev,mul_assoc,mul_comm,mul_left_comm,add_assoc,add_comm,add_left_comm] using hp
        exact tendsto_const_nhds.prodMk_nhds hlim

end MathGauge.RecursiveClosure.Counterexample
