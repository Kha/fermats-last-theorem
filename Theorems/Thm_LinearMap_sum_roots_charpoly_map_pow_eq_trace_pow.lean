import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_sum_roots_charpoly_map_pow_eq_trace_pow

set_option autoImplicit false

theorem LinearMap.sum_roots_charpoly_map_pow_eq_trace_pow {L : Type*} [Field L] {V : Type*}
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] (E : Type*) [Field E] [Algebra L E]
    [IsAlgClosed E] (T : V →ₗ[L] V) (n : ℕ) :
    (((T.charpoly).map (algebraMap L E)).roots.map (fun z => z ^ n)).sum =
      algebraMap L E (LinearMap.trace L V (T ^ n)) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_sum_roots_charpoly_map_pow_eq_trace_pow.solution
