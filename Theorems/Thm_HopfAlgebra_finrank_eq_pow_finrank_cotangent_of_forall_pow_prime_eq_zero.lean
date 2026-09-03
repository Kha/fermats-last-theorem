import Mathlib
import P2M.Util
import P2M.Sol.S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero

universe u v

theorem HopfAlgebra.finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (A : Type v) [CommRing A] [Bialgebra k A] [Module.Finite k A]
    (hA : ∀ a : A, Coalgebra.counit (R := k) a = 0 → a ^ p = 0) :
    Module.finrank k A =
      p ^ Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero.solution
