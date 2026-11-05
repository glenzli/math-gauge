import formal_oet.vol_01.ch_01_foundations.gauge_space
import formal_oet.vol_01.ch_01_foundations.operator_space
import formal_oet.vol_01.ch_01_foundations.metric_entropy
import formal_oet.vol_01.ch_02_operator_bounds.lip_matrix
import formal_oet.vol_01.ch_02_operator_bounds.single_channel
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Real.Basic
import OperatorLocalDegeneracy.ComponentPartition
import OperatorLocalDegeneracy.ComputationalFibers

namespace OperatorLocalDegeneracy

open formal_oet.vol_01.ch_01_foundations
open formal_oet.vol_01.ch_02_operator_bounds

variable {X I : Type} {bot : X} [Fintype I] [DecidableEq I]
variable (d : I → X → X → ENNReal)

/-- CH03-D04: 点态零化半径 -/
def r_null (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (y : X) (U : Set X) : ENNReal :=
  sSup { r : ENNReal | 0 < r ∧ r < ⊤ ∧ ∀ x ∈ U, d_in x y < r → d_out (ϕ.func x) (ϕ.func y) = 0 }

def r_null_single (ϕ : Operator X bot) (i j : I) (y : X) (U : Set X) : ENNReal :=
  r_null (d i) (d j) ϕ y U

def r_null_subfamily (ϕ : Operator X bot) (i : I) (J : Set I) (y : X) (U : Set X) : ENNReal :=
  r_null (d i) (subfamily_pseudometric d J) ϕ y U

/-- CH03-D05: 统一零化半径 -/
def r_null_uniform (d_in d_out : X → X → ENNReal) (ϕ : Operator X bot) (U : Set X) : ENNReal :=
  ⨅ y ∈ U, r_null d_in d_out ϕ y U

def N_matrix (ϕ : Operator X bot) (U : Set X) (i j : I) : ENNReal :=
  r_null_uniform (d i) (d j) ϕ U

def r_null_subfamily_uniform (ϕ : Operator X bot) (i : I) (J : Set I) (U : Set X) : ENNReal :=
  r_null_uniform (d i) (subfamily_pseudometric d J) ϕ U

#check @r_null
#check @r_null_uniform
#check @N_matrix
