import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import P2M.Util
import P2M.Sol.S_KatzModularForm_constantCoeff_ne_one_of_weight_two_zmod_eight

theorem KatzModularForm.constantCoeff_ne_one_of_weight_two_zmod_eight
    (F : KatzModularForm (ZMod 8) 2) (g : PowerSeries (ZMod 8))
    (hg : F.qExpansion = HahnSeries.ofPowerSeries ℤ (ZMod 8) g) :
    PowerSeries.constantCoeff g ≠ 1 := by p2m_exact_reverting @_root_.P2MW.S_KatzModularForm_constantCoeff_ne_one_of_weight_two_zmod_eight.solution
