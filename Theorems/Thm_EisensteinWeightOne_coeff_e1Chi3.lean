import Mathlib
import Definitions.Def_ModularForm_EisensteinChiNegThree
import P2M.Util
import P2M.Sol.S_EisensteinWeightOne_coeff_e1Chi3

open EisensteinWeightOne
theorem EisensteinWeightOne.coeff_e1Chi3 (n : ℕ) :
  (PowerSeries.coeff n) EisensteinWeightOne.e1Chi3 = if n = 0 then 1 else 6 * EisensteinWeightOne.sigmaChi n := by p2m_exact_reverting @_root_.P2MW.S_EisensteinWeightOne_coeff_e1Chi3.solution
