import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsIso f] :
    ∃ ι : Y.functionField ≃+* X.functionField,
      ∀ (V : Y.Opens) [Nonempty (V : Scheme.{u})] [Nonempty ((f ⁻¹ᵁ V : X.Opens) : Scheme.{u})] (t : Γ(Y, V)),
        ι (Y.germToFunctionField V t) = X.germToFunctionField (f ⁻¹ᵁ V) (f.app V t) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ringEquiv_functionField_germToFunctionField_eq_of_isIso.solution
