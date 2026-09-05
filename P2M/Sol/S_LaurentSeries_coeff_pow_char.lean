module

public import Mathlib
public import Definitions.Def_ModularCurve_X0
import P2M.Sol.S_ModularCurve_pow_char_eq_map_frobenius_qExpand
import P2M.Util

namespace P2MW.S_LaurentSeries_coeff_pow_char

set_option autoImplicit false

open HahnSeries ModularCurve

theorem solution {R : Type*} [CommRing R] (q : ℕ) [Fact q.Prime] [CharP R q]
    (f : LaurentSeries R) (n : ℤ) :
    (f ^ q).coeff n = if (q : ℤ) ∣ n then f.coeff (n / q) ^ q else 0 := by
  rw [pow_char_eq_map_frobenius_qExpand q f, HahnSeries.map_coeff]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : q.Prime).ne_zero
    rw [qExpand_coeff_mul, Int.mul_ediv_cancel_left _ hq0, frobenius_def]
  · rw [qExpand_coeff_of_not_dvd q f h, map_zero]
end S_LaurentSeries_coeff_pow_char
end P2MW

public section
attribute [-simp] ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ
set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

theorem LaurentSeries.coeff_pow_char {R : Type*} [CommRing R] (q : ℕ) [Fact q.Prime] [CharP R q]
    (f : LaurentSeries R) (n : ℤ) :
    (f ^ q).coeff n = if (q : ℤ) ∣ n then f.coeff (n / q) ^ q else 0 := by p2m_exact_reverting @_root_.P2MW.S_LaurentSeries_coeff_pow_char.solution
end
