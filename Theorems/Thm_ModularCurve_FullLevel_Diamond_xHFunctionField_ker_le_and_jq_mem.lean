import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import P2M.Util
import P2M.Sol.S_ModularCurve_FullLevel_Diamond_xHFunctionField_ker_le_and_jq_mem
attribute [-simp] ModularCurve.jqNModC_one

set_option autoImplicit false

theorem ModularCurve.FullLevel.Diamond.xHFunctionField_ker_le_and_jq_mem
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓgM' : ℓg ∣ M')
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker) :
    ModularCurve.xHFunctionField M' (ZMod.unitsMap hℓgM').ker ≤ ModularCurve.xHFunctionField (q ^ 2 * M') H₁ ∧
      ModularCurve.jq ∈ ModularCurve.xHFunctionField M' (ZMod.unitsMap hℓgM').ker := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_FullLevel_Diamond_xHFunctionField_ker_le_and_jq_mem.solution
