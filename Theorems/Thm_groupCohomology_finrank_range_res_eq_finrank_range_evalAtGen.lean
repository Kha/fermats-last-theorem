import Mathlib
import Definitions.Def_GroupCohomology_TateTwist
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_range_res_eq_finrank_range_evalAtGen

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finrank_range_res_eq_finrank_range_evalAtGen {k G : Type u} [Field k] [Group G] (A : Rep k G) [Finite G] [FiniteDimensional k A]
    (S : Subgroup G) [S.Normal] (t : G) (ht : t ∈ S) (htS : S ≤ Subgroup.zpowers t) :
    finrank k (LinearMap.range (ModuleCat.Hom.hom (H1InfRes A S).g)) =
      finrank k (LinearMap.range (groupCohomology.evalAtGen A t)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_range_res_eq_finrank_range_evalAtGen.solution
