import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_coeff_aeval_optionElim_C_add_X_sum_monomial_eq
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
attribute [-simp] AlgebraicCurve.Place.taylorRem_zero AlgebraicCurve.jetMatrix_order_zero AlgebraicCurve.Place.taylorCoeff_zero AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring

set_option autoImplicit false

theorem MvPolynomial.coeff_aeval_optionElim_C_add_X_sum_monomial_eq {K : Type*} [CommRing K] {e m : ℕ}
    (H : MvPolynomial (Option (Fin e)) K) (a : K) (w : Fin e → Fin m → K) (Y : Fin e → PowerSeries K)
    (hY : ∀ j (i : Fin m), PowerSeries.coeff (i : ℕ) (Y j) = w j i) (i : Fin m) :
    (MvPolynomial.aeval (fun o : Option (Fin e) =>
        Option.elim o (Polynomial.C a + Polynomial.X)
          (fun j => ∑ r : Fin m, Polynomial.monomial (r : ℕ) (w j r))) H).coeff i
      = PowerSeries.coeff (i : ℕ) (MvPolynomial.aeval (fun o : Option (Fin e) =>
        Option.elim o (PowerSeries.C a + PowerSeries.X) Y) H) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_coeff_aeval_optionElim_C_add_X_sum_monomial_eq.solution
