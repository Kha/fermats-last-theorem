import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_prime_of_not_dvd
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL

theorem ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_prime_of_not_dvd (N : ℕ) [Fact N.Prime] (data : ModularCurve.ModularPolynomialData N)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ¬ ℓ ∣ N) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (AlgebraicClosure (ZMod ℓ))))).map
      (algebraMap (Polynomial (AlgebraicClosure (ZMod ℓ))) (RatFunc (AlgebraicClosure (ZMod ℓ))))).Separable := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_prime_of_not_dvd.solution
