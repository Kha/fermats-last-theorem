import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isReduced_of_isClosedImmersion_of_isFinite_of_isReduced

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.isReduced_of_isClosedImmersion_of_isFinite_of_isReduced
    {k : Type u} [Field k] {X Z : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] [IsReduced X]
    (i : Z ⟶ X) [IsClosedImmersion i] : IsReduced Z := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isReduced_of_isClosedImmersion_of_isFinite_of_isReduced.solution
