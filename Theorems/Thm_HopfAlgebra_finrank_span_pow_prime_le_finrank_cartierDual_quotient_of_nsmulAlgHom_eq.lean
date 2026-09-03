import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_Basic
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finrank_span_pow_prime_le_finrank_cartierDual_quotient_of_nsmulAlgHom_eq

set_option autoImplicit false

universe u v

theorem HopfAlgebra.finrank_span_pow_prime_le_finrank_cartierDual_quotient_of_nsmulAlgHom_eq
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (H : Type v) [CommRing H] [HopfAlgebra k H] [Coalgebra.IsCocomm k H] [Module.Finite k H]
    (hp : PDivisibleGroup.Hopf.nsmulAlgHom k H p = (Algebra.ofId k H).comp (Bialgebra.counitAlgHom k H)) :
    Module.finrank k ↥(Submodule.span k (Set.range fun a : H => a ^ p)) ≤
      Module.finrank k
        (CartierDual k H ⧸ Ideal.span ((fun φ : CartierDual k H => φ ^ p) ''
          (RingHom.ker (Bialgebra.counitAlgHom k (CartierDual k H)) : Set (CartierDual k H)))) := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finrank_span_pow_prime_le_finrank_cartierDual_quotient_of_nsmulAlgHom_eq.solution
