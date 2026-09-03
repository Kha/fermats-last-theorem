import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_toZModPow_two_pow_eq_one_of_toZMod_eq_one

theorem PadicInt.toZModPow_two_pow_eq_one_of_toZMod_eq_one {p : ℕ} [hp : Fact p.Prime]
    {z : ℤ_[p]} (hz : PadicInt.toZMod z = 1) :
    PadicInt.toZModPow 2 (z ^ p) = 1 := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_toZModPow_two_pow_eq_one_of_toZMod_eq_one.solution
