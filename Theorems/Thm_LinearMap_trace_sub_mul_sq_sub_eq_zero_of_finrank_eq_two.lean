import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two

set_option autoImplicit false

theorem LinearMap.trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two
    {k : Type*} [Field k] {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hV : Module.finrank k V = 2) (Φ : V →ₗ[k] V) (t n : k) (hΦ : Φ * Φ - t • Φ + n • (1 : V →ₗ[k] V) = 0) :
    (LinearMap.trace k V Φ - t) * ((LinearMap.trace k V Φ - t) ^ 2 - (t ^ 2 - 4 * n)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_trace_sub_mul_sq_sub_eq_zero_of_finrank_eq_two.solution
