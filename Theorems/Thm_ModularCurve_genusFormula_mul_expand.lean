import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_genusFormula_mul_expand
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve
namespace ModularCurve
theorem genusFormula_mul_expand {M N : ℕ} (hM : M ≠ 0) (hN : N ≠ 0)
    (h : Nat.Coprime M N) :
    genusFormula (M * N) - 2 * genusFormula N + 1
      = ((dedekindPsi M : ℚ) - 2) * (dedekindPsi N : ℚ) / 12
        - ((nuTwo M : ℚ) - 2) * (nuTwo N : ℚ) / 4
        - ((nuThree M : ℚ) - 2) * (nuThree N : ℚ) / 3
        - ((cuspCount M : ℚ) - 2) * (cuspCount N : ℚ) / 2 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_genusFormula_mul_expand.solution
end ModularCurve
