module

public import Definitions.Def_ModularCurve_AtkinLehner
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_isFrickeAut

@[expose] public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ

open ModularCurve AlgebraicCurve IntermediateField
theorem ModularCurve.exists_isFrickeAut (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionField ℓ ≃ₐ[ℚ] modularFunctionField ℓ, IsFrickeAut ℓ σ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_isFrickeAut.solution
