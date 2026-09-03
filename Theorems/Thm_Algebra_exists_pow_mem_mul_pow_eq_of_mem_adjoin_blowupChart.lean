import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_pow_mem_mul_pow_eq_of_mem_adjoin_blowupChart

set_option autoImplicit false

theorem Algebra.exists_pow_mem_mul_pow_eq_of_mem_adjoin_blowupChart
    (C K : Type) [CommRing C] [Field K] [Algebra C K]
    (J : Ideal C) (a : C) (ha : a ∈ J) (ha0 : algebraMap C K a ≠ 0)
    (x : K) (hx : x ∈ Algebra.adjoin C {x : K | ∃ i ∈ J, x * algebraMap C K a = algebraMap C K i}) :
    ∃ (N : ℕ) (g : C), g ∈ J ^ N ∧ x * algebraMap C K a ^ N = algebraMap C K g := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_pow_mem_mul_pow_eq_of_mem_adjoin_blowupChart.solution
