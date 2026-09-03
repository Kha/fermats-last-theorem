import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_IsGamma0PowAt_variableChange

set_option autoImplicit false

universe u

open ModularCurve

theorem ModularCurve.IsGamma0PowAt.variableChange
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T) (p k : ℕ)
    (h : Polynomial T) (hh : ModularCurve.IsGamma0PowAt W p k h) :
    ModularCurve.IsGamma0PowAt (C • W) p k (ModularCurve.kernelVariableChangeDeg C (ModularCurve.gamma0PowDeg p k) h) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsGamma0PowAt_variableChange.solution
