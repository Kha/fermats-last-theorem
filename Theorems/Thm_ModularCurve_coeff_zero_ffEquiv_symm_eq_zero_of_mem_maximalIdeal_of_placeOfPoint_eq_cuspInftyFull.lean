import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_AlgebraicCurve_CurveModel
import P2M.Util
import P2M.Sol.S_ModularCurve_coeff_zero_ffEquiv_symm_eq_zero_of_mem_maximalIdeal_of_placeOfPoint_eq_cuspInftyFull
set_option autoImplicit false
open AlgebraicGeometry
theorem ModularCurve.coeff_zero_ffEquiv_symm_eq_zero_of_mem_maximalIdeal_of_placeOfPoint_eq_cuspInftyFull
    (p : ℕ) [NeZero p]
    (M : AlgebraicCurve.CurveModel ℚ ↥(ModularCurve.modularFunctionFieldFull p))
    (x : closedPoints M.C) (hx : M.placeOfPoint x = ModularCurve.cuspInftyFull p)
    (g : M.C.presheaf.stalk x.1)
    (hg : g ∈ IsLocalRing.maximalIdeal (M.C.presheaf.stalk x.1)) :
    (((M.ffEquiv.symm (algebraMap (M.C.presheaf.stalk x.1) M.C.functionField g) :
        ↥(ModularCurve.modularFunctionFieldFull p)) : LaurentSeries ℚ)).coeff 0 = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeff_zero_ffEquiv_symm_eq_zero_of_mem_maximalIdeal_of_placeOfPoint_eq_cuspInftyFull.solution
