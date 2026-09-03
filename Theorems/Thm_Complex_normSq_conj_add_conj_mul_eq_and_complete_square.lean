import Mathlib
import P2M.Util
import P2M.Sol.S_Complex_normSq_conj_add_conj_mul_eq_and_complete_square

set_option autoImplicit false

theorem Complex.normSq_conj_add_conj_mul_eq_and_complete_square
    (r z : ℂ) :
    (‖(starRingEnd ℂ) z + (starRingEnd ℂ) r * z‖ ^ 2 =
        ‖1 + r‖ ^ 2 * z.re ^ 2 + 4 * r.im * z.re * z.im + ‖1 - r‖ ^ 2 * z.im ^ 2) ∧
    (‖1 + r‖ ^ 2 + ‖1 - r‖ ^ 2 = 2 * (1 + ‖r‖ ^ 2)) ∧
    (‖1 + r‖ ≠ 0 →
      (1 - ‖r‖ ^ 2) ^ 2 + ‖(starRingEnd ℂ) z + (starRingEnd ℂ) r * z‖ ^ 2 =
        ‖1 + r‖ ^ 2 * ((z.re + 2 * r.im * z.im / ‖1 + r‖ ^ 2) ^ 2 +
          ((1 - ‖r‖ ^ 2) * Real.sqrt (z.im ^ 2 + ‖1 + r‖ ^ 2) / ‖1 + r‖ ^ 2) ^ 2)) ∧
    (‖1 - r‖ ≠ 0 →
      (1 - ‖r‖ ^ 2) ^ 2 + ‖(starRingEnd ℂ) z + (starRingEnd ℂ) r * z‖ ^ 2 =
        ‖1 - r‖ ^ 2 * ((z.im + 2 * r.im * z.re / ‖1 - r‖ ^ 2) ^ 2 +
          ((1 - ‖r‖ ^ 2) * Real.sqrt (z.re ^ 2 + ‖1 - r‖ ^ 2) / ‖1 - r‖ ^ 2) ^ 2)) := by p2m_exact_reverting @_root_.P2MW.S_Complex_normSq_conj_add_conj_mul_eq_and_complete_square.solution
