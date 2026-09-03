import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_map_two_injective_and_range_eq_ker_of_isZero_H1

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits groupCohomology Rep

theorem groupCohomology.map_two_injective_and_range_eq_ker_of_isZero_H1
    {k G : Type} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
    (hS : IsZero (groupCohomology (Rep.res S.subtype A) 1)) :
    Function.Injective (ModuleCat.Hom.hom (map (A := A.quotientToInvariants S) (B := A) (QuotientGroup.mk' S) (ofHom (A.ρ.quotientToInvariants_lift S)) 2)) ∧
      LinearMap.range (ModuleCat.Hom.hom (map (A := A.quotientToInvariants S) (B := A) (QuotientGroup.mk' S) (ofHom (A.ρ.quotientToInvariants_lift S)) 2)) =
        LinearMap.ker (ModuleCat.Hom.hom (map S.subtype (𝟙 (Rep.res S.subtype A)) 2)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_map_two_injective_and_range_eq_ker_of_isZero_H1.solution
