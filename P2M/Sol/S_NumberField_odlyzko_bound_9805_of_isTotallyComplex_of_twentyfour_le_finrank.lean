import Mathlib
import Theorems.Thm_Real_poitouKernel_admissible_and_archBound
import Theorems.Thm_NumberField_archTermDerived_le_log_abs_discr
import P2M.Util
namespace P2MW.S_NumberField_odlyzko_bound_9805_of_isTotallyComplex_of_twentyfour_le_finrank

set_option autoImplicit false

theorem solution
    (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (h24 : 24 ≤ Module.finrank ℚ K) :
    (9805 : ℤ) ^ Module.finrank ℚ K ≤ 1000 ^ Module.finrank ℚ K * |NumberField.discr K| := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, hpole, harch⟩ := Real.poitouKernel_admissible_and_archBound
  have hEF := NumberField.archTermDerived_le_log_abs_discr K
    (fun x : ℝ => Real.exp (-(11 / 100) * x ^ 2) / Real.cosh (x / 2)) h1 h2 h3 h4 h5 h6 h7 h8

  set n : ℕ := Module.finrank ℚ K with hn
  set AD : ℝ := Real.eulerMascheroniConstant + Real.log (4 * Real.pi)
        - ∫ x in Set.Ioi (0 : ℝ), (1 - (fun x : ℝ => Real.exp (-(11 / 100) * x ^ 2) / Real.cosh (x / 2)) x)
            / (Real.exp (x / 2) - Real.exp (-(x / 2))) with hAD
  set PT : ℝ := 2 * ∫ x in Set.Ioi (0 : ℝ),
        (fun x : ℝ => Real.exp (-(11 / 100) * x ^ 2) / Real.cosh (x / 2)) x
          * (Real.exp (x / 2) + Real.exp (-(x / 2))) with hPT
  have hPT : PT = 2 * Real.sqrt (100 * Real.pi / 11) := hpole
  have hsqrt : 0 ≤ Real.sqrt (100 * Real.pi / 11) := Real.sqrt_nonneg _
  have hlog : Real.log ((9805 : ℝ) / 2000) = Real.log (9805 / 1000) - Real.log 2 := by
    rw [show ((9805 : ℝ) / 2000) = (9805 / 1000) / 2 by norm_num, Real.log_div (by norm_num) two_ne_zero]

  have hslope : PT / 24 ≤ AD + Real.log 2 - Real.log (9805 / 1000) := by
    rw [hPT]; linarith
  have hnR : (24 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h24
  have hPTnn : 0 ≤ PT := by rw [hPT]; positivity
  have hfloor : (n : ℝ) * Real.log (9805 / 1000) ≤ (n : ℝ) * AD - PT + (n : ℝ) * Real.log 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hslope (by linarith : (0 : ℝ) ≤ (n : ℝ)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) - 24) (div_nonneg hPTnn (by norm_num : (0:ℝ) ≤ 24))]
  have hlogD : (n : ℝ) * Real.log (9805 / 1000) ≤ Real.log |(NumberField.discr K : ℝ)| :=
    hfloor.trans hEF

  have hD : (0 : ℝ) < |(NumberField.discr K : ℝ)| :=
    abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero K)
  have hpow : (0 : ℝ) < ((9805 : ℝ) / 1000) ^ n := by positivity
  have hle : ((9805 : ℝ) / 1000) ^ n ≤ |(NumberField.discr K : ℝ)| := by
    rw [← Real.log_le_log_iff hpow hD, Real.log_pow]; exact hlogD
  have hreal : (9805 : ℝ) ^ n ≤ 1000 ^ n * |(NumberField.discr K : ℝ)| := by
    calc (9805 : ℝ) ^ n = 1000 ^ n * ((9805 / 1000 : ℝ) ^ n) := by rw [← mul_pow]; norm_num
      _ ≤ 1000 ^ n * |(NumberField.discr K : ℝ)| := mul_le_mul_of_nonneg_left hle (by positivity)
  exact_mod_cast hreal
