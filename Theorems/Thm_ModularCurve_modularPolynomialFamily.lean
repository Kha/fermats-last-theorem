module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
import P2M.Util
import P2M.Sol.S_ModularCurve_modularPolynomialFamily

@[expose] public section

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.modularPolynomialFamily : ModularPolynomialFamily := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_modularPolynomialFamily.solution
