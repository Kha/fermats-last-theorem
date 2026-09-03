import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import P2M.Util
import P2M.Sol.S_ModularCurve_IsLevelPStructure_variableChange

theorem ModularCurve.IsLevelPStructure.variableChange {A : Type*} [CommRing A] {W : WeierstrassCurve A} {p : ℕ}
    {D : ModularCurve.LevelPData A} (h : ModularCurve.IsLevelPStructure W p D)
    (C : WeierstrassCurve.VariableChange A) :
    ModularCurve.IsLevelPStructure (C • W) p (D.variableChange C) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsLevelPStructure_variableChange.solution
