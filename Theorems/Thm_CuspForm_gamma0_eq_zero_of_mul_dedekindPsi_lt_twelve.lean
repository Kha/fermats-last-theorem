import Mathlib
import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_CuspForm_gamma0_eq_zero_of_mul_dedekindPsi_lt_twelve
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open scoped MatrixGroups

theorem CuspForm.gamma0_eq_zero_of_mul_dedekindPsi_lt_twelve (N : ℕ) [NeZero N] (k : ℤ)
    (h : k * (ModularCurve.dedekindPsi N : ℤ) < 12) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : f = 0 := by p2m_exact_reverting @_root_.P2MW.S_CuspForm_gamma0_eq_zero_of_mul_dedekindPsi_lt_twelve.solution
