import Definitions.Def_ModularCurve_WeierstrassLevelCarrier
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Sqf
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import P2M.Util
import P2M.Sol.S_WeierstrassCurve_IsCyclicGenKernel_variableChange

set_option autoImplicit false

universe u

open ModularCurve

theorem WeierstrassCurve.IsCyclicGenKernel.variableChange
    {T : Type u} [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T) (p k : ℕ)
    (h : Polynomial T) (hh : W.IsCyclicGenKernel p k h) :
    (C • W).IsCyclicGenKernel p k (ModularCurve.kernelVariableChangeDeg C (Nat.totient (p ^ k) / 2) h) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_IsCyclicGenKernel_variableChange.solution
