import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import P2M.Util
import P2M.Sol.S_HopfAlgebra_isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow

open scoped TensorProduct

universe u v

theorem HopfAlgebra.isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow
    (k : Type u) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (N : Type v) [CommRing N] [HopfAlgebra k N] [Coalgebra.IsCocomm k N] [Module.Finite k N]
    (hred : IsReduced (CartierDual k N)) (m : ℕ) (hN : Module.finrank k N = p ^ m) :
    IsLocalRing N := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_isLocalRing_of_isReduced_cartierDual_of_finrank_eq_prime_pow.solution
