import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval

set_option autoImplicit false

open Polynomial LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval
    (q : ℝ) (hq : 0 < q) (a b : ℂ) (hb : b ≠ 0) (hnorm : ‖b‖ = q)
    (hconj : (starRingEnd ℂ) a * b = (q : ℂ) * a) (X : ℂ) :
    (rsEulerPoly (a / q) (b / q ^ 2) ((starRingEnd ℂ) a / q) ((starRingEnd ℂ) b / q ^ 2) 0).eval ((q : ℂ) * X) =
      (rsEulerPoly (a / b) b⁻¹ a b 0).eval X := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval.solution
