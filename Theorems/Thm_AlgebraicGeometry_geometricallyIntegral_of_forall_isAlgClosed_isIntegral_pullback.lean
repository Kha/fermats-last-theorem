import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback
    {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]
    (hgeo : ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)),
      AlgebraicGeometry.IsIntegral (pullback f s)) :
    GeometricallyIntegral f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_forall_isAlgClosed_isIntegral_pullback.solution
