import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import P2M.Util
import P2M.Sol.S_ModularCurve_IsGamma1Point_variableChange

set_option autoImplicit false

theorem ModularCurve.IsGamma1Point.variableChange {A : Type*} [CommRing A] {W : WeierstrassCurve A} {ℓ : ℕ}
    {D : ModularCurve.LevelPData A} (h : ModularCurve.IsGamma1Point W ℓ D)
    (C : WeierstrassCurve.VariableChange A) :
    ModularCurve.IsGamma1Point (C • W) ℓ (D.variableChange C) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsGamma1Point_variableChange.solution
