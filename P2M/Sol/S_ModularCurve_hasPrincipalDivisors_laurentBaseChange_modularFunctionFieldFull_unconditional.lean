module

import P2M.Sol.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull
import P2M.Sol.S_ModularCurve_modularPolynomialFamily
import P2M.Util
public import Definitions.Def_AlgebraicCurve_DivisorClassGroup
public import Definitions.Def_ModularCurve_LaurentCoeff
public import Definitions.Def_ModularCurve_X0
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc

namespace P2MW.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional

open ModularCurve AlgebraicCurve

theorem solution (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull L modularPolynomialFamily N
end S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional
end P2MW

public section
attribute [-instance] ModularCurve.PhiGen.instNeZeroPhiGenCosetA
attribute [-simp] ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ
open ModularCurve AlgebraicCurve
theorem ModularCurve.hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N)) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional.solution
end
