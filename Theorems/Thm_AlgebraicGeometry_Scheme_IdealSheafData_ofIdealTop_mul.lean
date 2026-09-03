import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_mul {X : Scheme.{u}} (I J : Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I * J) = Scheme.IdealSheafData.ofIdealTop I * Scheme.IdealSheafData.ofIdealTop J := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul.solution
