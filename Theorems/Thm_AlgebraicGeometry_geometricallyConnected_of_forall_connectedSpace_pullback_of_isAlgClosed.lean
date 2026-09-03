import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
theorem AlgebraicGeometry.geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (x : R →+* k),
      ConnectedSpace ↥(pullback f (Spec.map (CommRingCat.ofHom x)))) :
    GeometricallyConnected f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_geometricallyConnected_of_forall_connectedSpace_pullback_of_isAlgClosed.solution
