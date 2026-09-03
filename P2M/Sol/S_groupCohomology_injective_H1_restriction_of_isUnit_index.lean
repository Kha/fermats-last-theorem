import Mathlib
import Theorems.Thm_groupCohomology_H1_subsingleton_of_isUnit_card
import P2M.Util
namespace P2MW.S_groupCohomology_injective_H1_restriction_of_isUnit_index

universe u

open CategoryTheory groupCohomology Module

theorem w2aux_inj
    {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {S : Subgroup G} [S.Normal]
    (hQ : Subsingleton (groupCohomology.H1 (A.quotientToInvariants S))) :
    Function.Injective (ModuleCat.Hom.hom (groupCohomology.H1InfRes A S).g) := by
  rw [← LinearMap.ker_eq_bot]
  have hexact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).1 (H1InfRes_exact A S)
  rw [← hexact]
  haveI h₁ : Subsingleton ((H1InfRes A S).X₁ : Type u) := hQ
  rw [LinearMap.range_eq_bot]
  exact LinearMap.ext fun x => by
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]

theorem solution
    {k G : Type u} [CommRing k] [Group G] {A : Rep k G} {S : Subgroup G} [S.Normal]
    [Fintype (G ⧸ S)] (hindex : IsUnit ((Fintype.card (G ⧸ S) : k))) :
    Function.Injective (ModuleCat.Hom.hom (groupCohomology.H1InfRes A S).g) :=
  w2aux_inj
    (groupCohomology.H1.subsingleton_of_isUnit_card (A.quotientToInvariants S) hindex)
