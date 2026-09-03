import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Topology

theorem AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ _ : IsDomain (T.presheaf.stalk η), IsDiscreteValuationRing (T.presheaf.stalk η) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_isDiscreteValuationRing_stalk_of_forall_specializes.solution
