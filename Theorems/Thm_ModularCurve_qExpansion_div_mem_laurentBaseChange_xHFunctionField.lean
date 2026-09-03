import Mathlib
import Definitions.Def_ModularCurve_XH
import P2M.Util
import P2M.Sol.S_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField

theorem ModularCurve.qExpansion_div_mem_laurentBaseChange_xHFunctionField (N : ℕ) [NeZero N]
    (H : Subgroup (ZMod N)ˣ) {k : ℤ}
    (f g : ModularForm (CohCarrier.GammaH N H : Subgroup (GL (Fin 2) ℝ)) k) (hg : g ≠ 0) :
    HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑f) /
        HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑g) ∈
      ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField N H) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_qExpansion_div_mem_laurentBaseChange_xHFunctionField.solution
