import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_flat_of_universallyOpen
    {X S : Scheme.{u}} (f : X ⟶ S) [GeometricallyIntegral f] [Flat f] [UniversallyOpen f]
    [IsIntegral S] : IsIntegral X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_GeometricallyIntegral_isIntegral_of_flat_of_universallyOpen.solution
