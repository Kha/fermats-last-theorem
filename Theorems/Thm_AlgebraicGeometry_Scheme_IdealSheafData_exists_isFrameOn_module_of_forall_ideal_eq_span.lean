import Mathlib
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_isFrameOn_module_of_forall_ideal_eq_span

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite

theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_isFrameOn_module_of_forall_ideal_eq_span
    {X : Scheme.{u}} (I : X.IdealSheafData) (W : X.Opens) (a : Γ(X, W))
    (ha : ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W),
      I.ideal U = Ideal.span {X.presheaf.map (homOfLE hU).op a} ∧
        X.presheaf.map (homOfLE hU).op a ∈ nonZeroDivisors Γ(X, U)) :
    ∃ e : Γ(I.module, W), I.moduleι.app W e = a ∧ Scheme.Modules.IsFrameOn e W := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_exists_isFrameOn_module_of_forall_ideal_eq_span.solution
