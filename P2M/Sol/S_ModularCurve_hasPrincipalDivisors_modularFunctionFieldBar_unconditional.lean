module

public import Definitions.Def_ModularCurve_ArithmeticGalois
public import Definitions.Def_ModularCurve_PhiGen
public import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar
public import Theorems.Thm_ModularCurve_modularPolynomialFamily
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional

open ModularCurve AlgebraicCurve

theorem solution (M : ℕ) [NeZero M] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M) :=
  hasPrincipalDivisors_modularFunctionFieldBar modularPolynomialFamily M

