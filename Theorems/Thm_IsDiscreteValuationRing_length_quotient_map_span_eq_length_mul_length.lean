import Mathlib
import P2M.Util
import P2M.Sol.S_IsDiscreteValuationRing_length_quotient_map_span_eq_length_mul_length

set_option autoImplicit false

theorem IsDiscreteValuationRing.length_quotient_map_span_eq_length_mul_length
    {D L : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [CommRing L] [IsDomain L] [IsLocalRing L]
    (φ : D →+* L) (hφ0 : Function.Injective φ)
    (f : D) (hf : f ≠ 0) :
    Module.length L (L ⧸ Ideal.span {φ f}) =
      Module.length D (D ⧸ Ideal.span {f}) * Module.length L (L ⧸ Ideal.map φ (IsLocalRing.maximalIdeal D)) := by p2m_exact_reverting @_root_.P2MW.S_IsDiscreteValuationRing_length_quotient_map_span_eq_length_mul_length.solution
