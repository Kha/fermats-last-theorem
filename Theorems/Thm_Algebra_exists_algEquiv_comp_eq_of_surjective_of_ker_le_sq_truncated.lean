import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated

set_option autoImplicit false

theorem Algebra.exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated
    (k : Type*) [Field k] (C : Type*) [CommRing C] [Algebra k C] [IsLocalRing C] [Module.Finite k C]
    (e M : ℕ)
    (α β : (MvPolynomial (Fin e) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)) →ₐ[k] C)
    (hα : Function.Surjective α) (hβ : Function.Surjective β)
    (hαk : RingHom.ker α ≤ (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k))) ^ 2)
    (hβk : RingHom.ker β ≤ (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k))) ^ 2) :
    ∃ θ : (MvPolynomial (Fin e) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)) ≃ₐ[k]
        (MvPolynomial (Fin e) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin e) k →+* k)) ^ (M + 1)),
      β.comp (θ : _ →ₐ[k] _) = α := by p2m_exact_reverting @_root_.P2MW.S_Algebra_exists_algEquiv_comp_eq_of_surjective_of_ker_le_sq_truncated.solution
