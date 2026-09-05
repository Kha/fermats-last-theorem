module

public import Mathlib
public import Definitions.Def_ModularCurve_LegendreJ
import P2M.Util

namespace P2MW.S_ModularCurve_legendreJ_eq_zero_iff

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "legendreJ"
p2m_open "ModularCurve"

theorem legendreJ_eq_zero_iff' {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 := by
  have hden : t ^ 2 * (t - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ (sub_ne_zero.mpr ht1))
  rw [legendreJ, div_eq_zero_iff, or_iff_left hden, mul_eq_zero, or_iff_right (pow_ne_zero _ h2)]
  exact pow_eq_zero_iff three_ne_zero

end ModularCurve

p2m_open "ModularCurve P2MW.S_ModularCurve_legendreJ_eq_zero_iff.ModularCurve"

theorem solution {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 :=
  ModularCurve.legendreJ_eq_zero_iff' h2 ht0 ht1
end S_ModularCurve_legendreJ_eq_zero_iff
end P2MW

public section
open ModularCurve
theorem ModularCurve.legendreJ_eq_zero_iff {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {t : K} (ht0 : t ≠ 0) (ht1 : t ≠ 1) :
    legendreJ t = 0 ↔ t ^ 2 - t + 1 = 0 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_legendreJ_eq_zero_iff.solution
end
