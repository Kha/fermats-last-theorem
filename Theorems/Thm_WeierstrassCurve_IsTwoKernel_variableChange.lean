import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_IsTwoKernel_variableChange

set_option autoImplicit false

universe u

open ModularCurve

theorem WeierstrassCurve.IsTwoKernel.variableChange
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (h : Polynomial T) (hh : W.IsTwoKernel h) :
    (C • W).IsTwoKernel (ModularCurve.kernelVariableChangeDeg C 1 h) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_IsTwoKernel_variableChange.solution
