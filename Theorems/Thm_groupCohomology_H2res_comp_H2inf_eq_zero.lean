import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_H2res_comp_H2inf_eq_zero

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology Rep
theorem groupCohomology.H2res_comp_H2inf_eq_zero
    {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal] :
    groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2 ≫
      groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2 = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_H2res_comp_H2inf_eq_zero.solution
