import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import P2M.Util
import P2M.Sol.S_ArithmeticFunction_sum_moebius_filter_dvd

open scoped ArithmeticFunction.Moebius
theorem ArithmeticFunction.sum_moebius_filter_dvd {n m : ℕ} (hn : n ≠ 0) (hm : m ∣ n) :
    ∑ f ∈ n.divisors, ArithmeticFunction.moebius (n / f) * (if m ∣ f then 1 else 0)
      = if m = n then 1 else 0 := by p2m_exact_reverting @_root_.P2MW.S_ArithmeticFunction_sum_moebius_filter_dvd.solution
