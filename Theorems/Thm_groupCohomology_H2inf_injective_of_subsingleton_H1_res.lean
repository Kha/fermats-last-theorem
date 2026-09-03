import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_H2inf_injective_of_subsingleton_H1_res

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology Rep
theorem groupCohomology.H2inf_injective_of_subsingleton_H1_res
    {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (H1 (Rep.res S.subtype A))] :
    Function.Injective
      (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2).hom := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_H2inf_injective_of_subsingleton_H1_res.solution
