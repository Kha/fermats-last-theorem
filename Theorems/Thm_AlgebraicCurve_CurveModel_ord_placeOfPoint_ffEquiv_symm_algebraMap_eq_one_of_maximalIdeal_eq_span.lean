import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry IsLocalRing

universe u v

theorem AlgebraicCurve.CurveModel.ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span
    {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]
    (M : AlgebraicCurve.CurveModel K L) (x : closedPoints M.C) (g : M.C.presheaf.stalk x.1)
    (hg : IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1) = Ideal.span {g}) :
    (M.placeOfPoint x).ord (M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g)) = 1 := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_CurveModel_ord_placeOfPoint_ffEquiv_symm_algebraMap_eq_one_of_maximalIdeal_eq_span.solution
