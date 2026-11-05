import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.EReal.Basic

#check (show (1 : EReal) - (1 : EReal) = 0 from rfl)
#check (show (1 : EReal) - (1 : EReal) = 0 by decide)
