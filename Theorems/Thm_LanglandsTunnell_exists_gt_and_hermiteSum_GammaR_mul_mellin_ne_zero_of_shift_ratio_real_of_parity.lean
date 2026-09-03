import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real_of_parity

set_option autoImplicit false

open Complex

theorem LanglandsTunnell.exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real_of_parity
    (m : ℕ) (a : ℚ) (ha : a ≠ 0) (u₃ : ℂ) (a₃ c : ZMod 2) (e : ℤ)
    (hne : (((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c))).Nonempty)
    (H : ℕ → ℝ → ℂ)
    (hA : ∀ (j : ℕ) (ε : ℝ), 0 < ε → ∃ R : ℝ, ∀ x : ℝ, R ≤ x →
      mellin (H j) (x : ℂ) ≠ 0 ∧
      ‖mellin (H j) ((x : ℂ) + 2) - (x : ℂ) / (2 * (Real.pi : ℂ) * (a : ℂ) ^ 2) * mellin (H j) (x : ℂ)‖ ≤ ε * x * ‖mellin (H j) (x : ℂ)‖)
    (hC : ∀ (j : ℕ), ∃ C R : ℝ, ∀ x : ℝ, R ≤ x →
      ‖mellin (H (j + 2)) (x : ℂ)‖ ≤ C * ‖mellin (H j) (x : ℂ)‖) :
    ∀ σ₀ : ℝ, ∃ s : ℝ, σ₀ < s ∧
      ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
              (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧
            ((T.2.1 : ZMod 2) = a₃ + c + (m : ZMod 2)) ∧ ((T.2.2 : ZMod 2) = (e : ZMod 2) + c)),
            ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) * (a : ℂ) ^ T.2.2 /
                ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                  (4 * (Real.pi : ℂ)) ^ T.1.1)) *
              Complex.Gammaℝ ((s : ℂ) + u₃ + (T.1.2 : ℂ)) * mellin (H T.2.1) ((s : ℂ) + (T.2.2 : ℂ) - 1) ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_exists_gt_and_hermiteSum_GammaR_mul_mellin_ne_zero_of_shift_ratio_real_of_parity.solution
