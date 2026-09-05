module

public import Mathlib
public import Definitions.Def_ModularCurve_X0
import P2M.Util
import P2M.Sol.S_ModularCurve_nonempty_modularPolynomialData

@[expose] public section

theorem ModularCurve.nonempty_modularPolynomialData (N : ℕ) [NeZero N] :
    Nonempty (ModularCurve.ModularPolynomialData N) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_nonempty_modularPolynomialData.solution
