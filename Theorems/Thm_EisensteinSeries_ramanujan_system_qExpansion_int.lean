import Mathlib
import P2M.Util
import P2M.Sol.S_EisensteinSeries_ramanujan_system_qExpansion_int

theorem EisensteinSeries.ramanujan_system_qExpansion_int
    (P Q R : PowerSeries ℤ)
    (hP : P = PowerSeries.mk fun n => if n = 0 then 1 else -24 * ∑ d ∈ n.divisors, (d : ℤ))
    (hQ : Q = PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3)
    (hR : R = PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) :
    12 * (PowerSeries.X * PowerSeries.derivative ℤ P) = P ^ 2 - Q ∧
      3 * (PowerSeries.X * PowerSeries.derivative ℤ Q) = P * Q - R ∧
        2 * (PowerSeries.X * PowerSeries.derivative ℤ R) = P * R - Q ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_EisensteinSeries_ramanujan_system_qExpansion_int.solution
