import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics
import P2M.Util
import P2M.Sol.S_ModularCurve_CuspSpace_sum_cuspWidth_eq_dedekindPsi
attribute [-instance] ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single

open OnePoint
open scoped MatrixGroups
theorem ModularCurve.CuspSpace.sum_cuspWidth_eq_dedekindPsi (N : ℕ) [NeZero N] (s : Finset (ModularCurve.CuspSpace N)) (hs : ∀ x : ModularCurve.CuspSpace N, x ∈ s) :
    ∑ c ∈ s, ModularCurve.CuspSpace.cuspWidth c = ModularCurve.dedekindPsi N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_CuspSpace_sum_cuspWidth_eq_dedekindPsi.solution
