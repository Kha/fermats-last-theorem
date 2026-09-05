module

public import Definitions.Def_ModularCurve_X0
public import Definitions.Def_ModularCurve_PhiGen
public import P2M.Util
public import P2M.Sol.S_ModularCurve_PhiGen_evalAtJ_injective

@[expose] public section

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.evalAtJ_injective : Function.Injective evalAtJ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_PhiGen_evalAtJ_injective.solution
