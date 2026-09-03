import Mathlib
import P2M.Util
import P2M.Sol.S_PowerSeries_coeff_eq_coeff_of_forall_coeff_eval_eq_zero
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv
attribute [-simp] AlgebraicCurve.Place.taylorRem_zero AlgebraicCurve.jetMatrix_order_zero AlgebraicCurve.Place.taylorCoeff_zero AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring

set_option autoImplicit false

open Polynomial

theorem PowerSeries.coeff_eq_coeff_of_forall_coeff_eval_eq_zero {K : Type*} [CommRing K]
    (f : Polynomial (PowerSeries K)) (a Y : PowerSeries K) (ha : f.eval a = 0)
    (hunit : IsUnit (PowerSeries.constantCoeff (f.derivative.eval a)))
    (h0 : PowerSeries.constantCoeff Y = PowerSeries.constantCoeff a) (m : ℕ)
    (hY : ∀ r, r < m → PowerSeries.coeff r (f.eval Y) = 0) :
    ∀ r, r < m → PowerSeries.coeff r Y = PowerSeries.coeff r a := by p2m_exact_reverting @_root_.P2MW.S_PowerSeries_coeff_eq_coeff_of_forall_coeff_eval_eq_zero.solution
