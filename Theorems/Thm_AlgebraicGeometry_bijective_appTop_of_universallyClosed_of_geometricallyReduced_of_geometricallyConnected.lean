import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected

open AlgebraicGeometry CategoryTheory

universe u

theorem AlgebraicGeometry.bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K))
    [UniversallyClosed f] [GeometricallyReduced f] [GeometricallyConnected f] :
    Function.Bijective f.appTop := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected.solution
