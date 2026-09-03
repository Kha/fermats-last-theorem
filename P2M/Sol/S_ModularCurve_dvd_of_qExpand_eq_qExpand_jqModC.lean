import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_CohCarrier_Level
import P2M.Util
namespace P2MW.S_ModularCurve_dvd_of_qExpand_eq_qExpand_jqModC

set_option autoImplicit false

open scoped MatrixGroups

namespace NonmemC3

open ModularCurve

theorem coeff_neg_one_jqModC (K : Type*) [Field K] : (jqModC K).coeff (-1) = 1 := by
  rw [jqModC, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_jNum, map_one]

end NonmemC3

theorem solution
    (K : Type*) [Field K] (d N : ℕ) [NeZero d] [NeZero N] (y : LaurentSeries K)
    (h : ModularCurve.qExpand K d y = ModularCurve.qExpand K N (ModularCurve.jqModC K)) : d ∣ N := by
  by_contra hd
  have h1 : (ModularCurve.qExpand K N (ModularCurve.jqModC K)).coeff ((N : ℤ) * (-1)) = 1 := by
    rw [ModularCurve.qExpand_coeff_mul, NonmemC3.coeff_neg_one_jqModC]
  have h2 : (ModularCurve.qExpand K d y).coeff ((N : ℤ) * (-1)) = 0 := by
    refine ModularCurve.qExpand_coeff_of_not_dvd d y ?_
    intro hdvd
    apply hd
    rw [mul_neg_one, Int.dvd_neg] at hdvd
    exact_mod_cast hdvd
  rw [h, h1] at h2
  exact one_ne_zero h2
