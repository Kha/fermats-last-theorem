import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finrank_le_finrank_span_pow_prime_mul_pow_finrank_cotangent

set_option autoImplicit false

universe u v

theorem HopfAlgebra.finrank_le_finrank_span_pow_prime_mul_pow_finrank_cotangent
    (K : Type u) [Field K] [IsAlgClosed K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (H : Type v) [CommRing H] [HopfAlgebra K H] [Module.Finite K H] :
    Module.finrank K H ≤
      Module.finrank K ↥(Submodule.span K (Set.range fun a : H => a ^ p)) *
        p ^ Module.finrank K (RingHom.ker (Bialgebra.counitAlgHom K H)).Cotangent := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finrank_le_finrank_span_pow_prime_mul_pow_finrank_cotangent.solution
