module

public import Mathlib
import P2M.Util
import P2M.Sol.S_LaurentSeries_coeff_pow_char

@[expose] public section
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem LaurentSeries.coeff_pow_char {R : Type*} [CommRing R] (q : ℕ) [Fact q.Prime] [CharP R q]
    (f : LaurentSeries R) (n : ℤ) :
    (f ^ q).coeff n = if (q : ℤ) ∣ n then f.coeff (n / q) ^ q else 0 := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_coeff_pow_char.solution
