import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_map_map_intCast_eq_of_charP
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

set_option autoImplicit false

theorem ModularCurve.ModularPolynomialData.map_map_intCast_eq_of_charP
    (p : ℕ) [Fact p.Prime] (data : ModularCurve.ModularPolynomialData p)
    (R : Type) [CommRing R] [CharP R p] :
    data.Φ.map (Polynomial.mapRingHom (Int.castRingHom R)) =
      (Polynomial.X - Polynomial.C (Polynomial.X ^ p)) * (Polynomial.X ^ p - Polynomial.C Polynomial.X) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_map_map_intCast_eq_of_charP.solution
