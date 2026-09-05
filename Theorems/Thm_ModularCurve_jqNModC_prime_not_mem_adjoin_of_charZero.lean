module

public import Definitions.Def_ModularCurve_JqCoeff
import P2M.Util
import P2M.Sol.S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero

@[expose] public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

open ModularCurve
theorem ModularCurve.jqNModC_prime_not_mem_adjoin_of_charZero {K : Type*} [Field K] [CharZero K] (p : ℕ) [hp : Fact (Nat.Prime p)] : jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_jqNModC_prime_not_mem_adjoin_of_charZero.solution
