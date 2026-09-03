import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isNilpotent_ker

set_option autoImplicit false

universe u

p2m_open "CategoryTheory AlgebraicGeometry~isAffine_of_isClosedImmersion_of_ker_mul_ker_eq_bot"

theorem AlgebraicGeometry.isAffine_of_isClosedImmersion_of_isNilpotent_ker
    {X₀ X : Scheme.{u}} (i : X₀ ⟶ X) [IsClosedImmersion i] [IsAffine X₀]
    (h : IsNilpotent i.ker) : IsAffine X := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isAffine_of_isClosedImmersion_of_isNilpotent_ker.solution
