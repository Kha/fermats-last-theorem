import Mathlib
import P2M.Util
import P2M.Sol.S_LocalParametrix_continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le

set_option autoImplicit false

open MeasureTheory FourierTransform

theorem LocalParametrix.continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    (r : V → ℂ) (hr : ContDiff ℝ (⊤ : ℕ∞) r) (s : ℝ) (hs : (Module.finrank ℝ V : ℝ) < s)
    (hb : ∀ n : ℕ, ∃ C : ℝ, ∀ ξ : V, ‖iteratedFDeriv ℝ n r ξ‖ ≤ C * (1 + ‖ξ‖) ^ (-(s + n))) :
    Continuous (𝓕 r) ∧ ContDiffOn ℝ (⊤ : ℕ∞) (𝓕 r) {0}ᶜ := by p2m_exact_reverting @_root_.P2MW.S_LocalParametrix_continuous_fourier_and_contDiffOn_compl_zero_of_norm_iteratedFDeriv_le.solution
