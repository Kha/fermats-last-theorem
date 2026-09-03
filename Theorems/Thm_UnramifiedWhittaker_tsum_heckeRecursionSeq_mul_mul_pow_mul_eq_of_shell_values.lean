import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import P2M.Util
import P2M.Sol.S_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_mul_pow_mul_eq_of_shell_values

set_option autoImplicit false

open UnramifiedWhittaker

theorem UnramifiedWhittaker.tsum_heckeRecursionSeq_mul_mul_pow_mul_eq_of_shell_values
    (N lam om y c w : ℂ) (k : ℕ) (I : ℕ → ℂ)
    (hI0 : ∀ m, m < k → I m = 0) (hIk : I k = c * w) (hI1 : ∀ m, k < m → I m = w)
    (hy : Summable fun m : ℕ => heckeRecursionSeq N lam om m * y ^ m) :
    (∑' m : ℕ, heckeRecursionSeq N lam om m * I m * y ^ m) * (1 - lam / N * y + om / N * y ^ 2) =
      w * (c * heckeRecursionSeq N lam om k * y ^ k +
        (heckeRecursionSeq N lam om (k + 1) - c * (lam / N) * heckeRecursionSeq N lam om k) *
          y ^ (k + 1) +
        (c - 1) * (om / N) * heckeRecursionSeq N lam om k * y ^ (k + 2)) := by p2m_exact_reverting @_root_.P2MW.S_UnramifiedWhittaker_tsum_heckeRecursionSeq_mul_mul_pow_mul_eq_of_shell_values.solution
