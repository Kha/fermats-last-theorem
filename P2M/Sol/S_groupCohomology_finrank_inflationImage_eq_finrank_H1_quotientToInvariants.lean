import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
namespace P2MW.S_groupCohomology_finrank_inflationImage_eq_finrank_H1_quotientToInvariants

open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [Field k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal] :
    finrank k (inflationImage A S) = finrank k (H1 (A.quotientToInvariants S)) :=
  LinearMap.finrank_range_of_inj
    ((ModuleCat.mono_iff_injective _).1 (inferInstance : Mono (H1InfRes A S).f))
