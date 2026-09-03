import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq

set_option autoImplicit false

theorem MvPolynomial.bijective_algHom_truncated_of_forall_exists_sub_mem_sq
    (k : Type*) [Field k] (N M : ℕ)
    (θ : (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)) →ₐ[k]
      (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)))
    (hθ : ∀ j : Fin N, ∃ t, θ t - Ideal.Quotient.mk _ (MvPolynomial.X j) ∈
      (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k))) ^ 2) :
    Function.Bijective θ := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_bijective_algHom_truncated_of_forall_exists_sub_mem_sq.solution
