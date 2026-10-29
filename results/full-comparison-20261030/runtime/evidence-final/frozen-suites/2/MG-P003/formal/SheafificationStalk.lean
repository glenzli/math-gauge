import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Limits

/-!
The genuine small Zariski/topological sheafification comparison on a singleton
neighborhood colimit. This uses Mathlib's actual stalk, defined as a colimit over
open neighborhoods, and its actual sheafification unit. The comparison between
the smooth big-site sheafification in task.md and this small-site restriction
has not been established here.
-/

namespace MathGauge.PublicProof.Semilocal

noncomputable section

open CategoryTheory TopologicalSpace

universe u

/-- The canonical sheafification morphism induces an isomorphism on the actual
abelian-group stalk. This is the small-site version of the one-point base case. -/
theorem singleton_neighborhood_comparison_isIso
    (X : TopCat.{u}) (F : TopCat.Presheaf AddCommGrpCat.{u} X) (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) F)) := by
  exact TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat F

end

end MathGauge.PublicProof.Semilocal
