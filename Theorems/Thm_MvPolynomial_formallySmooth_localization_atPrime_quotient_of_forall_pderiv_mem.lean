import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem

set_option autoImplicit false

open MvPolynomial IsLocalRing

theorem MvPolynomial.formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem
    (R : Type) [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I J : Ideal (MvPolynomial (Fin n) R)) (hIJ : I ≤ J) [hJ : J.IsMaximal]
    (hJac : ∀ v ∈ I, (∀ i : Fin n, MvPolynomial.pderiv i v ∈ J) → v ∈ J * I) :
    haveI : (J.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
        rw [Ideal.mk_ker]; exact hIJ)
    Algebra.FormallySmooth R (Localization.AtPrime (J.map (Ideal.Quotient.mk I))) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_formallySmooth_localization_atPrime_quotient_of_forall_pderiv_mem.solution
