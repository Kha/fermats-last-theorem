import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent

set_option autoImplicit false

universe u v

theorem HopfAlgebra.finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : Type v) [CommRing H] [HopfAlgebra k H] [Module.Finite k H] :
    Module.finrank k
        (H ⧸ Ideal.span ((fun a : H => a ^ p) '' (RingHom.ker (Bialgebra.counitAlgHom k H) : Set H))) =
      p ^ Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k H)).Cotangent := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finrank_quotient_span_pow_prime_eq_pow_finrank_cotangent.solution
