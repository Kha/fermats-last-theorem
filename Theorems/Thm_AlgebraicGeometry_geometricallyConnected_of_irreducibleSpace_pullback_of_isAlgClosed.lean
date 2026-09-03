import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (k : Type u) [Field k] [Algebra K k] [IsAlgClosed k]
    [IrreducibleSpace ↑(pullback f (Spec.map (CommRingCat.ofHom (algebraMap K k))))] :
    GeometricallyConnected f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_geometricallyConnected_of_irreducibleSpace_pullback_of_isAlgClosed.solution
