module

public import Mathlib
public import P2M.Util
public import P2M.Sol.S_LaurentSeries_coeff_neg_one_mul_inv_pow_uniformizer

@[expose] public section
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem LaurentSeries.coeff_neg_one_mul_inv_pow_uniformizer {R : Type*} [CommRing R]
    (q : ℕ) [Fact q.Prime] [CharP R q]
    (ω s v : LaurentSeries R) (hω : ∀ n < 0, ω.coeff n = 0)
    (hs1 : s.coeff 1 = 1) (hs : ∀ n < 1, s.coeff n = 0) (hv : s ^ q * v = 1) :
    (ω * v).coeff (-1) = ω.coeff ((q : ℤ) - 1) := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_coeff_neg_one_mul_inv_pow_uniformizer.solution
