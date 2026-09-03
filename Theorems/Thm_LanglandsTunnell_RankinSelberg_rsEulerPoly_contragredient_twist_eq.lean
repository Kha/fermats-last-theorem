import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_RankinSelberg_rsEulerPoly_contragredient_twist_eq

set_option autoImplicit false

open Polynomial LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.rsEulerPoly_contragredient_twist_eq
    (a b t : ℂ) (hb : b ≠ 0) (ht : t ≠ 0) :
    rsEulerPoly ((t * a) / (t ^ 2 * b)) (t ^ 2 * b)⁻¹ (t * a) (t ^ 2 * b) 0 =
      rsEulerPoly (a / b) b⁻¹ a b 0 := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_RankinSelberg_rsEulerPoly_contragredient_twist_eq.solution
