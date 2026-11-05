import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.EReal.Basic
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers
import OperatorLocalDegeneracy.NullificationRadius
import OperatorLocalDegeneracy.ThresholdClassification

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

/-- CH03-D07: 全有界接口 -/
def IsTotallyBounded (d_metric : X → X → ENNReal) (U : Set X) : Prop :=
  ∀ ε : ENNReal, 0 < ε → covering_number d_metric ε U < ⊤

/-- CH03-D08: 映射熵差 -/
noncomputable def entropy_diff (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (ε : ENNReal) (U : Set X) : EReal :=
  metric_entropy d_out ε (ϕ.func '' U) - metric_entropy d_in ε U

noncomputable def subfamily_entropy_diff (ϕ : Operator X bot) (J_in J_out : Set I) (ε : ENNReal) (U : Set X) : EReal :=
  subfamily_metric_entropy d J_out ε (ϕ.func '' U) - subfamily_metric_entropy d J_in ε U

/-- CH03-P18-01: 命题 3.15 (i) 严格低于统一半径的输入点对输出零距 -/
theorem prop_3_15_i (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hdist : d_in x y < r_null_uniform d_in d_out ϕ U) :
    d_out (ϕ.func x) (ϕ.func y) = 0 := by
  have h_le := biInf_le (fun z => r_null d_in d_out ϕ z U) hy
  have hlt : d_in x y < r_null d_in d_out ϕ y U := lt_of_lt_of_le hdist h_le
  exact prop_3_11_lt_sSup d_in d_out ϕ U y hx hlt

/-- CH03-P18-02: 命题 3.15 (ii) 输出正分离推出输入距离≥统一半径 -/
theorem prop_3_15_ii (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X)
    {x y : X} (hx : x ∈ U) (hy : y ∈ U)
    (hsep : 0 < d_out (ϕ.func x) (ϕ.func y)) :
    r_null_uniform d_in d_out ϕ U ≤ d_in x y := by
  by_contra! hlt
  have hzero := prop_3_15_i d_in d_out ϕ U hx hy hlt
  rw [hzero] at hsep
  exact (lt_self_iff_false 0).mp hsep
