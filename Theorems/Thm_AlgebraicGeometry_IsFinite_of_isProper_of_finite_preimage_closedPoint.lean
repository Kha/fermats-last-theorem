import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_IsFinite_of_isProper_of_finite_preimage_closedPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem AlgebraicGeometry.IsFinite.of_isProper_of_finite_preimage_closedPoint
    {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (hfin : (f.base ⁻¹' {(IsLocalRing.closedPoint R : PrimeSpectrum R)}).Finite) :
    IsFinite f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_IsFinite_of_isProper_of_finite_preimage_closedPoint.solution
