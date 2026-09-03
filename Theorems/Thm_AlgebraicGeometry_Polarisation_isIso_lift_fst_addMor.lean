import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisationRosati
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Polarisation_isIso_lift_fst_addMor

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GoodReductionJacobian AlgebraicGeometry.Polarisation

theorem AlgebraicGeometry.Polarisation.isIso_lift_fst_addMor
    {S : Type u} [CommRing S] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of S)) (L : RelativeGroupLaw S f) :
    IsIso (pullback.lift (pullback.fst f f) (addMor f L) (addMor_over f L).symm) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Polarisation_isIso_lift_fst_addMor.solution
