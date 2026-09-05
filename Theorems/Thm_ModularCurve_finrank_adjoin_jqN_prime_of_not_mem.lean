module

public import Definitions.Def_ModularCurve_X0
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem

@[expose] public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

open ModularCurve
theorem ModularCurve.finrank_adjoin_jqN_prime_of_not_mem (F : IntermediateField ℚ (LaurentSeries ℚ)) (hj : jq ∈ F) (p : ℕ) [hp : Fact (Nat.Prime p)] (hpF : jqN p ∉ F) : Module.finrank F (IntermediateField.adjoin F ({jqN p} : Set (LaurentSeries ℚ))) = p + 1 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.solution
