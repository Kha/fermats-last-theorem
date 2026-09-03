import Mathlib
import P2M.Util
import P2M.Sol.S_DrinfeldCurve_LocalChart_exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul
attribute [-instance] DrinfeldCurve.instAlgebraCoordRing DrinfeldCurve.instCommRingCoordRing
attribute [-simp] DrinfeldCurve.LocalChart.ChartPresentation.mk.sizeOf_spec DrinfeldCurve.LocalChart.ChartPresentation.mk.injEq

set_option autoImplicit false

open IsLocalRing Polynomial

theorem DrinfeldCurve.LocalChart.exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul
    (q : ℕ) [Fact q.Prime] (W : Type) [CommRing W] [IsLocalRing W]
    (π : W) (hπ : maximalIdeal W = Ideal.span {π}) (hq : (q : W) ∈ maximalIdeal W) :
    ∃ E : Polynomial (MvPolynomial (Fin 2) W),
      ∏ a : Fin q, ∏ b : Fin q,
          (Polynomial.X - Polynomial.C
            (((a : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 0 + ((b : ℕ) : MvPolynomial (Fin 2) W) * MvPolynomial.X 1) :
            Polynomial (MvPolynomial (Fin 2) W)) =
        Polynomial.X ^ (q ^ 2)
          - Polynomial.C (∑ i ∈ Finset.range (q + 1),
              (MvPolynomial.X 0 : MvPolynomial (Fin 2) W) ^ ((q - 1) * i) * MvPolynomial.X 1 ^ ((q - 1) * (q - i))) *
            Polynomial.X ^ q
          + Polynomial.C (((MvPolynomial.X 0 : MvPolynomial (Fin 2) W) * MvPolynomial.X 1 ^ q
              - MvPolynomial.X 0 ^ q * MvPolynomial.X 1) ^ (q - 1)) * Polynomial.X
          + Polynomial.C (MvPolynomial.C π) * E := by p2m_exact_reverting @_root_.P2MW.S_DrinfeldCurve_LocalChart_exists_prod_prod_X_sub_C_eq_moore_add_C_C_mul.solution
