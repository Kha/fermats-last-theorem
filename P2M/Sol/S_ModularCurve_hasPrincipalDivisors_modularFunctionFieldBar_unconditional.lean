module

public import Definitions.Def_ModularCurve_ArithmeticGalois
public import Definitions.Def_ModularCurve_PhiGen
import P2M.Sol.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar
import P2M.Sol.S_ModularCurve_modularPolynomialFamily
import P2M.Util

namespace P2MW.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional

open ModularCurve AlgebraicCurve

theorem solution (M : ℕ) [NeZero M] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M) :=
  hasPrincipalDivisors_modularFunctionFieldBar modularPolynomialFamily M
end S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
end P2MW

public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ
open ModularCurve AlgebraicCurve
theorem ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (M : ℕ) [NeZero M] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional.solution
end
