import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_mul {X Y : Scheme.{u}}
    (I J : Y.IdealSheafData) (f : X ⟶ Y) :
    (I * J).comap f = I.comap f * J.comap f := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul.solution
