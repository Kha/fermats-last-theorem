import Mathlib
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_HeckeEis_finrank_coeffH1par_le_two_mul_dimFormula
attribute [-instance] ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] HeckeEis.coe_linePow ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

set_option autoImplicit false

open scoped MatrixGroups

theorem HeckeEis.finrank_coeffH1par_le_two_mul_dimFormula (N : ℕ) [NeZero N] (n : ℕ) (hn : 2 ≤ n) (hne : Even n) :
    (Module.finrank ℂ (HeckeEis.coeffH1par ((HeckeEis.binaryFormRepSL ℂ n).comp (CongruenceSubgroup.Gamma0 N).subtype)) : ℚ)
      ≤ 2 * ((((n + 2) : ℚ) - 1) * (ModularCurve.genusFormula N - 1) + (((n + 2) / 4 : ℕ) : ℚ) * (ModularCurve.nuTwo N : ℚ)
        + (((n + 2) / 3 : ℕ) : ℚ) * (ModularCurve.nuThree N : ℚ) + (((n + 2) : ℚ) / 2 - 1) * (ModularCurve.cuspCount N : ℚ)) := by p2m_exact_reverting @_root_.P2MW.S_HeckeEis_finrank_coeffH1par_le_two_mul_dimFormula.solution
