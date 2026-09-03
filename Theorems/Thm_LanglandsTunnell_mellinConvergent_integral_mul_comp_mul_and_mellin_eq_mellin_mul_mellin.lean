import Mathlib.Analysis.MellinTransform
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin

set_option autoImplicit false

open MeasureTheory

theorem LanglandsTunnell.mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin
    (φ g : ℝ → ℂ) (z : ℂ)
    (hφm : AEStronglyMeasurable φ (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hgm : AEStronglyMeasurable g (Measure.restrict volume (Set.Ioi (0 : ℝ))))
    (hφ : MellinConvergent φ (1 - z)) (hg : MellinConvergent g z) :
    MellinConvergent (fun r : ℝ => ∫ t in Set.Ioi (0 : ℝ), φ t * g (r * t)) z ∧
      mellin (fun r : ℝ => ∫ t in Set.Ioi (0 : ℝ), φ t * g (r * t)) z = mellin φ (1 - z) * mellin g z := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_mellinConvergent_integral_mul_comp_mul_and_mellin_eq_mellin_mul_mellin.solution
