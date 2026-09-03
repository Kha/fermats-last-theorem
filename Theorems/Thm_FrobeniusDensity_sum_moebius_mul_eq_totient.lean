import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_sum_moebius_mul_eq_totient

theorem FrobeniusDensity.sum_moebius_mul_eq_totient (n : ℕ) (hn : 0 < n) :
    ∑ f ∈ n.divisors, (ArithmeticFunction.moebius (n / f)) * (f : ℤ) = (Nat.totient n : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_sum_moebius_mul_eq_totient.solution
