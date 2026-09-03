import Mathlib
import P2M.Util
import P2M.Sol.S_Polynomial_exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq

universe u

theorem Polynomial.exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S] [IsLocalRing S]
    (D : Polynomial R) (hD : ∃ i, IsUnit (D.coeff i))
    (x : Fin (D.natDegree + 1) → S) (hx : ∀ i j, x i - x j ∈ IsLocalRing.maximalIdeal S → i = j) :
    ∃ i, IsUnit (Polynomial.aeval (x i) D) := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq.solution
