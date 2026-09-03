import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
namespace P2MW.S_groupCohomology_finrank_H1_eq_finrank_inflationImage_add_finrank_range_res

open CategoryTheory Module groupCohomology

universe u

theorem solution {k G : Type u} [Field k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
    [FiniteDimensional k (H1 A)] :
    finrank k (H1 A) = finrank k (inflationImage A S) +
      finrank k (LinearMap.range (ModuleCat.Hom.hom (H1InfRes A S).g)) := by
  have hexact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (H1InfRes_exact A S)
  haveI : FiniteDimensional k ((H1InfRes A S).X₂ : Type u) := ‹FiniteDimensional k (H1 A)›
  have h := LinearMap.finrank_range_add_finrank_ker (ModuleCat.Hom.hom (H1InfRes A S).g)
  rw [← hexact, add_comm] at h
  exact h.symm
