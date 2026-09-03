import Mathlib
import Definitions.Def_ModularForm_EisensteinChiNegThree
import P2M.Util
import P2M.Sol.S_EisensteinWeightOne_tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal

set_option autoImplicit false

theorem EisensteinWeightOne.tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal (σ : ℂ) (hσ : 0 < σ.im) :
    (∑' n : ℕ, ((PowerSeries.coeff n EisensteinWeightOne.e1Chi3 : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * σ)) =
      ∑' p : ℤ × ℤ, Complex.exp (2 * (Real.pi : ℂ) * Complex.I * σ *
        ((p.1 : ℂ) ^ 2 + (p.1 : ℂ) * (p.2 : ℂ) + (p.2 : ℂ) ^ 2)) := by p2m_exact_reverting @_root_.P2MW.S_EisensteinWeightOne_tsum_coeff_e1Chi3_mul_exp_eq_tsum_exp_hexagonal.solution
