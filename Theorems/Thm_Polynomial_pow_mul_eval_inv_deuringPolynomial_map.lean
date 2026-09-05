module

public import Mathlib
public import Definitions.Def_Polynomial_DeuringPolynomial
import P2M.Util
import P2M.Sol.S_Polynomial_pow_mul_eval_inv_deuringPolynomial_map

@[expose] public section

open Polynomial
theorem Polynomial.pow_mul_eval_inv_deuringPolynomial_map {F : Type*} [Field F] (q : ℕ) (t : F)
    (ht : t ≠ 0) :
    t ^ ((q - 1) / 2) * ((deuringPolynomial q).map (Int.castRingHom F)).eval t⁻¹
      = ((deuringPolynomial q).map (Int.castRingHom F)).eval t := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_pow_mul_eval_inv_deuringPolynomial_map.solution
