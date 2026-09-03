import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_exists_pow_mul_mem_range

set_option autoImplicit false
theorem IsDiscreteValuationRing.exists_pow_mul_mem_range
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (t : R) (ht : t ≠ 0) (ht' : t ∈ IsLocalRing.maximalIdeal R) (x : K) :
    ∃ N : ℕ, ∃ r : R, algebraMap R K r = algebraMap R K t ^ N * x := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_exists_pow_mul_mem_range.solution
