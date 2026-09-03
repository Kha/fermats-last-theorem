import Mathlib
import P2M.Util
import P2M.Sol.S_RingHom_exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed

theorem RingHom.exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
    {R S K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    [Field K] [IsAlgClosed K] (χ : R →+* K)
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.comap (algebraMap R S) = RingHom.ker χ) :
    ∃ χ' : S →+* K, χ'.comp (algebraMap R S) = χ ∧ RingHom.ker χ' = Q := by p2m_exact_reverting @_root_.P2MW.S_RingHom_exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed.solution
