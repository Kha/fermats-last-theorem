import Mathlib
import P2M.Util
import P2M.Sol.S_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
set_option autoImplicit false

theorem ValuationSubring.ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP
    (A : ValuationSubring (AlgebraicClosure ℚ)) {k : Type*} [Field k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (red : A →+* k) (c : A) :
    red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal A := by p2m_exact_reverting @_root_.P2MW.S_ValuationSubring_ringHom_apply_eq_zero_iff_mem_maximalIdeal_of_charP.solution
