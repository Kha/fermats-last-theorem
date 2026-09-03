import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem

set_option autoImplicit false
theorem IsDiscreteValuationRing.mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    (a v : 𝒪) (k M : ℕ)
    (hk : a ∉ IsLocalRing.maximalIdeal 𝒪 ^ (k + 1))
    (h : a * v ∈ IsLocalRing.maximalIdeal 𝒪 ^ M) :
    v ∈ IsLocalRing.maximalIdeal 𝒪 ^ (M - k) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_mem_maximalIdeal_pow_sub_of_mul_mem_of_not_mem.solution
