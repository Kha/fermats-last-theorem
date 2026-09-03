import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_prod_prod_X_sub_C_natCast_mul_add_eq_moore

set_option autoImplicit false

open IsLocalRing

theorem DrinfeldCurve.LocalChart.prod_prod_X_sub_C_natCast_mul_add_eq_moore
    (q : ℕ) [Fact q.Prime] (R : Type) [CommRing R] [CharP R q] :
    ∏ a : Fin q, ∏ b : Fin q,
        (Polynomial.X - Polynomial.C
          (((a : ℕ) : MvPolynomial (Fin 2) R) * MvPolynomial.X 0 + ((b : ℕ) : MvPolynomial (Fin 2) R) * MvPolynomial.X 1) :
          Polynomial (MvPolynomial (Fin 2) R)) =
      Polynomial.X ^ (q ^ 2)
        - Polynomial.C (∑ i ∈ Finset.range (q + 1),
            (MvPolynomial.X 0 : MvPolynomial (Fin 2) R) ^ ((q - 1) * i) * MvPolynomial.X 1 ^ ((q - 1) * (q - i))) *
          Polynomial.X ^ q
        + Polynomial.C (((MvPolynomial.X 0 : MvPolynomial (Fin 2) R) * MvPolynomial.X 1 ^ q
            - MvPolynomial.X 0 ^ q * MvPolynomial.X 1) ^ (q - 1)) * Polynomial.X := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_prod_prod_X_sub_C_natCast_mul_add_eq_moore.solution
