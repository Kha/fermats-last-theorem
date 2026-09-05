module

public import Definitions.Def_ModularCurve_ArithmeticGalois
public import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar

@[expose] public section

open ModularCurve AlgebraicCurve
theorem ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar.solution
