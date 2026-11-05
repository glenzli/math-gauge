
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

open Finset

def centers : Finset (Option ℝ) := { some (-2), some 0, some 2 }

example : some (-2) ∈ centers := mem_insert_self _ _
example : some 0 ∈ centers := mem_insert_of_mem (mem_insert_self _ _)
example : some 2 ∈ centers := mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
