import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_bijective_app_of_forall_isAffineOpen

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

theorem AlgebraicGeometry.bijective_app_of_forall_isAffineOpen {X B : Scheme.{u}} (p : X ⟶ B)
    (h : ∀ U : B.Opens, IsAffineOpen U → Function.Bijective (p.app U)) (U : B.Opens) :
    Function.Bijective (p.app U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_bijective_app_of_forall_isAffineOpen.solution
