import Mathlib
import P2M.Util
import P2M.Sol.S_IsRegularLocalRing_of_maximalIdeal_eq_span_of_mem_sq_of_ringKrullDim_eq_two

set_option autoImplicit false

theorem IsRegularLocalRing.of_maximalIdeal_eq_span_of_mem_sq_of_ringKrullDim_eq_two
    {B : Type*} [CommRing B] [IsNoetherianRing B] [IsLocalRing B]
    (π u v : B) (hgen : IsLocalRing.maximalIdeal B = Ideal.span {π, u, v})
    (hπ : π ∈ IsLocalRing.maximalIdeal B ^ 2) (hdim : ringKrullDim B = 2) :
    IsRegularLocalRing B := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_of_maximalIdeal_eq_span_of_mem_sq_of_ringKrullDim_eq_two.solution
