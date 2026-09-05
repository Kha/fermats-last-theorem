module

public import Mathlib
public import Definitions.Def_Polynomial_DeuringPolynomial
import P2M.Util
import P2M.Sol.S_Polynomial_eval_one_deuringPolynomial_map

@[expose] public section

open Polynomial
theorem Polynomial.eval_one_deuringPolynomial_map {F : Type*} [Field F] (q : ℕ) [Fact q.Prime]
    [CharP F q] : ((deuringPolynomial q).map (Int.castRingHom F)).eval 1 = (-1) ^ ((q - 1) / 2) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_eval_one_deuringPolynomial_map.solution
