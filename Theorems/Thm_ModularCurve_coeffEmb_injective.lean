module

public import Definitions.Def_ModularCurve_LaurentCoeff
public import P2M.Util
public import P2M.Sol.S_ModularCurve_coeffEmb_injective

@[expose] public section

theorem ModularCurve.coeffEmb_injective (L : Type*) [Field L] [Algebra ℚ L] : Function.Injective (ModularCurve.coeffEmb L) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffEmb_injective.solution
