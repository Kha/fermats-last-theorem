import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import P2M.Util
import P2M.Sol.S_HopfAlgebra_free_and_finrank_eq_prime_pow_of_withConv_equiv_of_natCard_eq

set_option autoImplicit false

open scoped PadicInt

theorem HopfAlgebra.free_and_finrank_eq_prime_pow_of_withConv_equiv_of_natCard_eq
    (p : ℕ) [Fact p.Prime]
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H] [Module.Finite ℤ_[p] H] [Module.Flat ℤ_[p] H]
    [Coalgebra.IsCocomm ℤ_[p] H]
    {M : Type} [Finite M] (e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ M) (a : ℕ) (hM : Nat.card M = p ^ a) :
    Module.Free ℤ_[p] H ∧ Module.finrank ℤ_[p] H = p ^ a := by p2m_exact_reverting @_root_.P2MW.S_HopfAlgebra_free_and_finrank_eq_prime_pow_of_withConv_equiv_of_natCard_eq.solution
