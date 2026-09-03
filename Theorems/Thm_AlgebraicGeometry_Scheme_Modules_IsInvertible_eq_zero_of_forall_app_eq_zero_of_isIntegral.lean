import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_forall_app_eq_zero_of_isIntegral

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.eq_zero_of_forall_app_eq_zero_of_isIntegral
    {X : Scheme.{u}} [IsIntegral X] {M N : X.Modules} (hN : Scheme.Modules.IsInvertible N) (f : M ⟶ N)
    (U : X.Opens) (hU : Nonempty U) (h : ∀ V : X.Opens, V ≤ U → f.app V = 0) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_eq_zero_of_forall_app_eq_zero_of_isIntegral.solution
