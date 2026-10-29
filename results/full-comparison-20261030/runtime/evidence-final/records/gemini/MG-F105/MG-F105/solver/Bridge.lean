import Core

open scoped Pointwise
namespace MathGauge.F105
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem slice_difference (A : Finset G) (H : AddSubgroup G) (x : G)
    {b c : G} (hb : b ∈ cosetSlice A H x) (hc : c ∈ cosetSlice A H x) :
    b - c ∈ H := by
  have h := H.sub_mem ((mem_cosetSlice A H x b).mp hb).2
    ((mem_cosetSlice A H x c).mp hc).2
  convert h using 1 <;> abel

theorem lift_cover (A F : Finset G) (H : AddSubgroup G) (x : G)
    (h : A ⊆ F + (cosetSlice A H x - cosetSlice A H x)) : Covers A H F := by
  intro a ha
  obtain ⟨t, ht, d, hd, htd⟩ := Finset.mem_add.mp (h ha)
  obtain ⟨b, hb, c, hc, hbc⟩ := Finset.mem_sub.mp hd
  refine ⟨t, ht, ?_⟩
  have heq : a - t = b - c := by
    rw [← htd, ← hbc]
    abel
  rw [heq]
  exact slice_difference A H x hb hc

end MathGauge.F105
