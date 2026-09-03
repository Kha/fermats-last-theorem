import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_ringHom_apply_eq_zero_of_mem_maximalIdeal

theorem ValuationSubring.ringHom_apply_eq_zero_of_mem_maximalIdeal
    {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (f : A →+* k) {x : A} (hx : x ∈ IsLocalRing.maximalIdeal A) : f x = 0 := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_ringHom_apply_eq_zero_of_mem_maximalIdeal.solution
