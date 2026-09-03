import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Basic
import P2M.Util
import P2M.Sol.S_ModularCurve_dvd_sq_sub_one_div_of_isCoprime_of_not_dvd

theorem ModularCurve.dvd_sq_sub_one_div_of_isCoprime_of_not_dvd (p m : ℕ) (hp : p.Prime) (a1 tau : ℤ) (h1 : IsCoprime a1 (m : ℤ)) (hpm : ¬ p ∣ m) (hC1 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * tau) (hC2 : (24 * m : ℤ) ∣ a1 * ((p : ℤ) - 1) * (tau ^ 2 - (p : ℤ) ^ 11 * ((p : ℤ) + 1))) : m ∣ (p ^ 2 - 1) / 24 := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_dvd_sq_sub_one_div_of_isCoprime_of_not_dvd.solution
