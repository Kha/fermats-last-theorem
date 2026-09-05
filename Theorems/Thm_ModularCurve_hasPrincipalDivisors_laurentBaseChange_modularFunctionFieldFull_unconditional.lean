module

public import Definitions.Def_ModularCurve_ArithmeticGalois
import P2M.Util
import P2M.Sol.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional

@[expose] public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ
open ModularCurve AlgebraicCurve
theorem ModularCurve.hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional.solution
