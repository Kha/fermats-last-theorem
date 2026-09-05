module

public import Definitions.Def_ModularCurve_ArithmeticGalois
public import Definitions.Def_ModularCurve_PhiGen
public import Theorems.Thm_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull
import P2M.Util

@[expose] public section
namespace P2MW.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar

noncomputable section
open IntermediateField

open ModularCurve AlgebraicCurve

theorem solution (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) hΦ N

end
