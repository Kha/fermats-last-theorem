import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import P2M.Util
import P2M.Sol.S_LanglandsTunnell_CubicInduction_mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum

set_option autoImplicit false

open Polynomial LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum
    (P : Polynomial ℂ) (hP0 : P.coeff 0 = 1) (hP3 : P.natDegree ≤ 3) :
    PowerSeries.mk (sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3)) * (P : PowerSeries ℂ) = 1 ∧
    (∀ n : ℕ, ‖sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3) n‖ ≤
      (max 1 (‖P.coeff 1‖ + ‖P.coeff 2‖ + ‖P.coeff 3‖)) ^ n) ∧
    ∀ x : ℂ, ‖x‖ * max 1 (‖P.coeff 1‖ + ‖P.coeff 2‖ + ‖P.coeff 3‖) < 1 →
      P.eval x ≠ 0 ∧
      HasSum (fun n : ℕ => sphericalTorusValue (-P.coeff 1) (P.coeff 2) (-P.coeff 3) n * x ^ n)
        (P.eval x)⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_LanglandsTunnell_CubicInduction_mk_sphericalTorusValue_mul_coe_eq_one_and_hasSum.solution
