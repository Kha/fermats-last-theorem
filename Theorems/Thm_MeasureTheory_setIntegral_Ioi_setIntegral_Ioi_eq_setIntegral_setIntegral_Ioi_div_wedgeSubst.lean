import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst

set_option autoImplicit false

open MeasureTheory Set

theorem MeasureTheory.setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst
    (H : ℝ → ℝ → ℂ) (hHm : Measurable (Function.uncurry H))
    (hHi : Integrable (Function.uncurry H)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))))
    (v : ℝ) (hv : 0 < v) :
    ∫ u in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), H t u =
      ∫ σ in Ioi (0 : ℝ), ∫ w in Ioi (v / σ),
        ((v ^ 2 / w ^ 3 : ℝ) : ℂ) * H (v * (σ * w - v) / w ^ 2) (v / w) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_setIntegral_Ioi_setIntegral_Ioi_eq_setIntegral_setIntegral_Ioi_div_wedgeSubst.solution
