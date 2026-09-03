import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isConnected_preimage_singleton_of_forall_connectedSpace_pullback_of_isAlgClosed

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isConnected_preimage_singleton_of_forall_connectedSpace_pullback_of_isAlgClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Y), ConnectedSpace ↥(Limits.pullback f s))
    (y : ↥Y) : _root_.IsConnected (f.base ⁻¹' {y}) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isConnected_preimage_singleton_of_forall_connectedSpace_pullback_of_isAlgClosed.solution
