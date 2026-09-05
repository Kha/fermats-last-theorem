module

public import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero

@[expose] public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open ModularCurve
theorem ModularCurve.exists_monic_evalAtJ_jqN_eq_zero (N : ℕ) [NeZero N] : ∃ P : Polynomial (Polynomial ℤ), P.Monic ∧ P.eval₂ evalAtJ (jqN N) = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.solution
