import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.GroupTheory.OrderOfElement
import P2M.Util
import P2M.Sol.S_FrobeniusDensity_sum_moebius_mul_pos

open scoped Classical in
theorem FrobeniusDensity.sum_moebius_mul_pos {G : Type*} [Group G] [Finite G] (σ : G) :
    0 < ∑ f ∈ (orderOf σ).divisors,
      (ArithmeticFunction.moebius (orderOf σ / f)) * (f : ℤ) := by p2m_exact_reverting @_root_.P2MW.S_FrobeniusDensity_sum_moebius_mul_pos.solution
