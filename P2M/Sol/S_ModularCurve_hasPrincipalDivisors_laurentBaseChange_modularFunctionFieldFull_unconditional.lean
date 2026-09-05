module

public import Definitions.Def_ModularCurve_ArithmeticGalois
public import Definitions.Def_ModularCurve_PhiGen
public import Theorems.Thm_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull
public import Theorems.Thm_ModularCurve_modularPolynomialFamily
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull_unconditional

open ModularCurve AlgebraicCurve

theorem solution (L : Type*) [Field L] [Algebra ℚ L]
    (N : ℕ) [NeZero N] : HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N)) :=
  hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull L modularPolynomialFamily N

