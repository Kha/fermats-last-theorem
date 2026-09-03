import Mathlib
import Definitions.Def_ModularForm_EisensteinChiNegThree
import P2M.Util
import P2M.Sol.S_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub

open EisensteinWeightOne
theorem EisensteinWeightOne.three_dvd_coeff_mul_e1Chi3_sub (g : PowerSeries ℤ) (n : ℕ) :
  3 ∣ (PowerSeries.coeff n) (g * EisensteinWeightOne.e1Chi3) - (PowerSeries.coeff n) g := by p2m_exact_reverting @_root_.P2MW.S_EisensteinWeightOne_three_dvd_coeff_mul_e1Chi3_sub.solution
