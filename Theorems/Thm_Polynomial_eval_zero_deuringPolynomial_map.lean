import Mathlib
import Definitions.Def_Polynomial_DeuringPolynomial
import P2M.Util
import P2M.Sol.S_Polynomial_eval_zero_deuringPolynomial_map

open Polynomial
theorem Polynomial.eval_zero_deuringPolynomial_map {F : Type*} [Field F] (q : ℕ) :
    ((deuringPolynomial q).map (Int.castRingHom F)).eval 0 = 1 := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_eval_zero_deuringPolynomial_map.solution
