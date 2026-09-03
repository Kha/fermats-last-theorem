import Mathlib
import P2M.Util
import P2M.Sol.S_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport

set_option autoImplicit false

open MeasureTheory

theorem MeasureTheory.contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ]
    {M P E : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : X → M) (hc : Continuous c) (w : X → ℝ) (hw : Continuous w) (hwc : HasCompactSupport w)
    (Ψ : M × P → E) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ) (hΨc : HasCompactSupport Ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : P => ∫ x, w x • Ψ (c x, p) ∂μ) := by p2m_exact_reverting @_root_.P2MW.S_MeasureTheory_contDiff_integral_smul_comp_of_contDiff_of_hasCompactSupport.solution
