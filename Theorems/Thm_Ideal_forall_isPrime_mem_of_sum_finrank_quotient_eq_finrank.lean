import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank

set_option autoImplicit false

theorem Ideal.forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank
    (F R : Type) [Field F] [CommRing R] [Algebra F R] [Module.Finite F R] [IsReduced R]
    (S : Finset (Ideal R)) (hS : ∀ 𝔭 ∈ S, 𝔭.IsPrime)
    (hsum : ∑ 𝔭 ∈ S, Module.finrank F (R ⧸ 𝔭) = Module.finrank F R) :
    ∀ 𝔭 : Ideal R, 𝔭.IsPrime → 𝔭 ∈ S := by p2m_exact_reverting @_root_.P2MW.S_Ideal_forall_isPrime_mem_of_sum_finrank_quotient_eq_finrank.solution
