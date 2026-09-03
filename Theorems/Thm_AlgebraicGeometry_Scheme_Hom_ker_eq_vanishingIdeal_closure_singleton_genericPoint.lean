import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_ker_eq_vanishingIdeal_closure_singleton_genericPoint

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.Hom.ker_eq_vanishingIdeal_closure_singleton_genericPoint
    {C Y : Scheme.{u}} (f : C ⟶ Y) [IsIntegral C] [QuasiCompact f] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (X := Y) ⟨closure ({f.base (genericPoint C)} : Set Y), isClosed_closure⟩ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_ker_eq_vanishingIdeal_closure_singleton_genericPoint.solution
