
import formal_oet.vol_01.ch_01_foundations.gauge_space
import Mathlib.Data.ENNReal.Basic
import OperatorLocalDegeneracy.ThresholdClassification

namespace OperatorLocalDegeneracy

example : classify_channel (ENNReal.ofReal (1 / 2)) ⊤ 1 1 = ThresholdType.T11 := by
  dsimp [classify_channel]
  have h1 : ENNReal.ofReal (1 / 2) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]; norm_num
  rw [if_pos h1]
  rfl

example : classify_channel (ENNReal.ofReal (1 / 5)) 0 1 1 = ThresholdType.T10 := by
  dsimp [classify_channel]
  have h1 : ENNReal.ofReal (1 / 5) ≤ 1 := by
    rw [ENNReal.ofReal_le_one]; norm_num
  have h2 : ¬ ((1 : ENNReal) ≤ 0) := by norm_num
  rw [if_pos h1, if_neg h2]

example : classify_channel 2 2 1 1 = ThresholdType.T01 := by
  dsimp [classify_channel]
  have h1 : ¬ ((2 : ENNReal) ≤ 1) := by norm_num
  have h2 : (1 : ENNReal) ≤ 2 := by norm_num
  rw [if_neg h1, if_pos h2]

example : classify_channel 2 0 1 1 = ThresholdType.T00 := by
  dsimp [classify_channel]
  have h1 : ¬ ((2 : ENNReal) ≤ 1) := by norm_num
  have h2 : ¬ ((1 : ENNReal) ≤ 0) := by norm_num
  rw [if_neg h1, if_neg h2]
