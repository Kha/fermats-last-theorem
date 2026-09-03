import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.MellinTransform
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_hermite_fourfold_twoSheet_reflection_eq_sum_filter

set_option autoImplicit false

open Complex

theorem LanglandsTunnell.hermite_fourfold_twoSheet_reflection_eq_sum_filter
    (m : ℕ) (a₃ ē : ZMod 2) (Fp Fm u v w : ℂ) :
    (Fp * ∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (u - v - w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ a₃.val * Fm * (∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (-u - v + w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ ē.val * Fm * (∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (u - v + w) ^ (m - 2 * r)) +
      (-1 : ℂ) ^ ē.val * (-1 : ℂ) ^ a₃.val * Fp * (∑ r ∈ Finset.range (m / 2 + 1),
          (-1 : ℂ) ^ r * (m.factorial : ℂ) / ((r.factorial : ℂ) * ((m - 2 * r).factorial : ℂ) * (4 * (Real.pi : ℂ)) ^ r) *
            (-u - v - w) ^ (m - 2 * r)) =
      2 * ∑ T ∈ ((Finset.range (m + 1) ×ˢ Finset.range (m + 1)) ×ˢ (Finset.range (m + 1) ×ˢ Finset.range (m + 1))).filter
          (fun T : (ℕ × ℕ) × (ℕ × ℕ) => T.1.2 + T.2.1 + T.2.2 + 2 * T.1.1 = m ∧ ((T.1.2 : ZMod 2) = ē + a₃)),
          ((-1 : ℂ) ^ T.1.1 * (m.factorial : ℂ) /
              ((T.1.1.factorial : ℂ) * (T.1.2.factorial : ℂ) * (T.2.1.factorial : ℂ) * (T.2.2.factorial : ℂ) *
                (4 * (Real.pi : ℂ)) ^ T.1.1)) *
            (-1 : ℂ) ^ (T.2.1 + T.2.2) * (Fp + (-1 : ℂ) ^ (ē + (T.2.2 : ZMod 2)).val * Fm) *
            u ^ T.1.2 * v ^ T.2.1 * w ^ T.2.2 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_hermite_fourfold_twoSheet_reflection_eq_sum_filter.solution
