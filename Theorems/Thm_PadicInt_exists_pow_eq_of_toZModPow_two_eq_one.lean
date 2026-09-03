import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_exists_pow_eq_of_toZModPow_two_eq_one

theorem PadicInt.exists_pow_eq_of_toZModPow_two_eq_one {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {u : ℤ_[p]} (hu : PadicInt.toZModPow 2 u = 1) :
    ∃ z : ℤ_[p], PadicInt.toZMod z = 1 ∧ z ^ p = u := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_pow_eq_of_toZModPow_two_eq_one.solution
