import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing
    {A : Type u} [CommRing A] [IsDomain A] (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [Flat f]
    [IsIntegral ↑(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap A L))))] :
    IsIntegral X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_of_flat_of_isIntegral_pullback_specMap_of_isFractionRing.solution
