import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_H1_eq_finrank_inflationImage_add_finrank_range_res

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finrank_H1_eq_finrank_inflationImage_add_finrank_range_res {k G : Type u} [Field k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
    [FiniteDimensional k (H1 A)] :
    finrank k (H1 A) = finrank k (inflationImage A S) +
      finrank k (LinearMap.range (ModuleCat.Hom.hom (H1InfRes A S).g)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_H1_eq_finrank_inflationImage_add_finrank_range_res.solution
