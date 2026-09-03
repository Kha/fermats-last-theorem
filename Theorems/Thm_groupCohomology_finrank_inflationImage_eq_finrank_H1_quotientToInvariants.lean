import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_inflationImage_eq_finrank_H1_quotientToInvariants

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finrank_inflationImage_eq_finrank_H1_quotientToInvariants {k G : Type u} [Field k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal] :
    finrank k (inflationImage A S) = finrank k (H1 (A.quotientToInvariants S)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_inflationImage_eq_finrank_H1_quotientToInvariants.solution
