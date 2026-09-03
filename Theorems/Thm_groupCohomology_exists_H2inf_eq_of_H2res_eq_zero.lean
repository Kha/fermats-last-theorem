import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_H2inf_eq_of_H2res_eq_zero

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology Rep
theorem groupCohomology.exists_H2inf_eq_of_H2res_eq_zero
    {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (H1 (Rep.res S.subtype A))] (x : H2 A)
    (hx : (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2).hom x = 0) :
    ∃ y : H2 (A.quotientToInvariants S),
      (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2).hom y = x := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_H2inf_eq_of_H2res_eq_zero.solution
