import Mathlib
import Definitions.Def_ModularCurve_EichlerMass
import P2M.Util
import P2M.Sol.S_ModularCurve_ssCountFormula_eq_genus
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve
namespace ModularCurve
theorem ssCountFormula_eq_genus {N q : ℕ} (hN : N ≠ 0) (hq : q.Prime)
    (hqN : ¬ q ∣ N) :
    ssCountFormula N q = genusFormula (N * q) - 2 * genusFormula N + 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_ssCountFormula_eq_genus.solution
end ModularCurve
