import Mathlib.Analysis.SpecialFunctions.Pow.Real
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow

set_option autoImplicit false

theorem
LanglandsTunnell.CubicInduction.expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow
    {ι : Type*} [Fintype ι] (e : ι → ℂ) (j : ι → ℕ) (c : ι → ℂ)
    (hinj : Function.Injective fun i => (e i, j i))
    (θ₀ : ℝ) (F R : ℝ → ℂ)
    (hF : ∀ y : ℝ, 0 < y → y ≤ 1 → F y = ∑ i, c i * ((y : ℂ) ^ e i * (Real.log y : ℂ) ^ j i) + R y)
    (hR : ∃ K : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 → ‖R y‖ ≤ K * y ^ θ₀)
    (hray : ∃ C : ℝ, ∀ y₁ : ℝ, 0 < y₁ → y₁ ≤ 1 → ‖F y₁‖ ≤ C * y₁ ^ θ₀) :
    ∀ i, (e i).re < θ₀ → c i = 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_expLogSum_coeff_eq_zero_of_re_lt_of_norm_le_rpow.solution
