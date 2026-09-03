import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import P2M.Util
import P2M.Sol.S_UnramifiedWhittaker_norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow

set_option autoImplicit false

open UnramifiedWhittaker

theorem UnramifiedWhittaker.norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow
    (q κ : ℝ) (hq : 1 ≤ q) (hκ : 0 ≤ κ) (lam om : ℂ)
    (hlam : ‖lam‖ ≤ q ^ κ) (hom : ‖om‖ ≤ q ^ κ) (m : ℕ) :
    ‖heckeRecursionSeq (q : ℂ) lam om m‖ ≤ ((m : ℝ) + 1) * (2 * q ^ κ) ^ m := by p2m_exact_reverting @_root_.P2MW.S_UnramifiedWhittaker_norm_heckeRecursionSeq_le_mul_pow_of_norm_le_rpow.solution
