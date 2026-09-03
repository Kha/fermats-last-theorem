import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_length_ker_lsmul_quotient_maximalIdeal_pow_le

set_option autoImplicit false
theorem IsDiscreteValuationRing.length_ker_lsmul_quotient_maximalIdeal_pow_le
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] (a : 𝒪) (n : ℕ) :
    Module.length 𝒪 (LinearMap.ker
        (LinearMap.lsmul 𝒪 (𝒪 ⧸ IsLocalRing.maximalIdeal 𝒪 ^ (n + 1)) a)) ≤
      Module.length 𝒪 (𝒪 ⧸ Ideal.span {a}) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_length_ker_lsmul_quotient_maximalIdeal_pow_le.solution
