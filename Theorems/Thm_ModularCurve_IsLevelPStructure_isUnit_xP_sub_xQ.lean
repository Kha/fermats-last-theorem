import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import P2M.Util
import P2M.Sol.S_ModularCurve_IsLevelPStructure_isUnit_xP_sub_xQ

set_option autoImplicit false

theorem ModularCurve.IsLevelPStructure.isUnit_xP_sub_xQ
    {T : Type*} [CommRing T] (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ)
    (W : WeierstrassCurve T) (D : ModularCurve.LevelPData T) (hD : ModularCurve.IsLevelPStructure W ℓ D) :
    IsUnit (D.xP - D.xQ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IsLevelPStructure_isUnit_xP_sub_xQ.solution
