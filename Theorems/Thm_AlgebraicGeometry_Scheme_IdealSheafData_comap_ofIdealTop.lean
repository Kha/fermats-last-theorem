import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_ofIdealTop
    {X Y : Scheme.{u}} (I : Ideal Γ(Y, ⊤)) (f : X ⟶ Y) :
    (Scheme.IdealSheafData.ofIdealTop I).comap f
      = Scheme.IdealSheafData.ofIdealTop (I.map f.appTop.hom) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_comap_ofIdealTop.solution
