import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.IdealSheafData.range_moduleIota_app_and_injective
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    Set.range (I.moduleι.app U) = (I.ideal U : Set Γ(X, U)) ∧
      Function.Injective (I.moduleι.app U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective.solution
