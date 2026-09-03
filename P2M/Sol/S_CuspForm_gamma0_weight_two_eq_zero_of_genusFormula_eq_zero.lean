import Mathlib
import Definitions.Def_ModularCurve_GenusNumerics
import Theorems.Thm_CuspForm_finrank_gamma0_weight_two_le_genusFormula
import Theorems.Thm_CuspForm_finiteDimensional_cuspForm
import P2M.Util
namespace P2MW.S_CuspForm_gamma0_weight_two_eq_zero_of_genusFormula_eq_zero
attribute [-instance] HeckeEis.instFiniteIndexHeckeUpper ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite
attribute [-simp] ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.CuspSpace.cuspDenomAux_infty
attribute [-simp] ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one

set_option autoImplicit false

namespace Ws23
namespace GenusZeroVanishing

theorem finrank_eq_zero (N : ℕ) [NeZero N] (hg : ModularCurve.genusFormula N = 0) :
    Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) = 0 := by
  have h := CuspForm.finrank_gamma0_weight_two_le_genusFormula N
  rw [hg] at h
  exact_mod_cast Nat.eq_zero_of_le_zero (by exact_mod_cast h)

theorem main (N : ℕ) [NeZero N] (hg : ModularCurve.genusFormula N = 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f = 0 := by
  haveI := CuspForm.finiteDimensional_cuspForm N 2
  haveI : Subsingleton (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
    Module.finrank_zero_iff.1 (finrank_eq_zero N hg)
  exact Subsingleton.elim f 0

end Ws23.GenusZeroVanishing

theorem solution (N : ℕ) [NeZero N]
    (hg : ModularCurve.genusFormula N = 0) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f = 0 :=
  Ws23.GenusZeroVanishing.main N hg f
