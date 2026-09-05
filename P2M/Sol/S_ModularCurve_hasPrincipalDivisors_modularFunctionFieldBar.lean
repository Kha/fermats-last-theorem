module

public import Definitions.Def_ModularCurve_ArithmeticGalois
public import Definitions.Def_ModularCurve_PhiGen
import P2M.Sol.S_ModularCurve_hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull
import P2M.Util

namespace P2MW.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar

noncomputable section
open IntermediateField

open ModularCurve AlgebraicCurve

theorem solution (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) hΦ N

end
end S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar
end P2MW

public section
open ModularCurve AlgebraicCurve
theorem ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.solution
end
