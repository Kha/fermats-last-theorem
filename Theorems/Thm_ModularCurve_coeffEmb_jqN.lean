module

public import Definitions.Def_ModularCurve_JqCoeff
public import Definitions.Def_ModularCurve_LaurentCoeff
public import P2M.Util
public import P2M.Sol.S_ModularCurve_coeffEmb_jqN

@[expose] public section

open ModularCurve
theorem ModularCurve.coeffEmb_jqN (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ) [NeZero N] :
    coeffEmb L (jqN N) = jqNModC L N := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_coeffEmb_jqN.solution
