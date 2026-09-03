import Mathlib
import P2M.Util
import P2M.Sol.S_Ideal_isDomain_quotient_of_isReduced_of_isCompl_of_existsUnique_minimalPrimes

set_option autoImplicit false

theorem Ideal.isDomain_quotient_of_isReduced_of_isCompl_of_existsUnique_minimalPrimes
    (R : Type) [CommRing R] [IsReduced R] (I J : Ideal R) (hIJ : IsCompl I J)
    [Nontrivial (R ⧸ I)]
    (huniq : ∃! 𝔭 : Ideal R, 𝔭 ∈ (⊥ : Ideal R).minimalPrimes ∧ I ≤ 𝔭) :
    IsDomain (R ⧸ I) := by p2m_exact_reverting @_root_.P2MW.S_Ideal_isDomain_quotient_of_isReduced_of_isCompl_of_existsUnique_minimalPrimes.solution
