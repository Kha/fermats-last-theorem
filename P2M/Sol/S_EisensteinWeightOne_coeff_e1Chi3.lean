import Mathlib.RingTheory.PowerSeries.Basic
import Definitions.Def_ModularForm_EisensteinChiNegThree
import P2M.Util
namespace P2MW.S_EisensteinWeightOne_coeff_e1Chi3

open EisensteinWeightOne

theorem solution (n : ℕ) :
    PowerSeries.coeff n e1Chi3 = if n = 0 then 1 else 6 * sigmaChi n := by
  rw [e1Chi3, PowerSeries.coeff_mk]
