import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq

set_option autoImplicit false

theorem MvPolynomial.nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq
    (k : Type*) [Field k] (N M : ℕ)
    (x : (MvPolynomial (Fin (N + 1)) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
    (hx₁ : x ∈ Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)))
    (hx₂ : x ∉ (Ideal.map (Ideal.Quotient.mk ((RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)))
        (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k))) ^ 2) :
    Nonempty (((MvPolynomial (Fin (N + 1)) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin (N + 1)) k →+* k)) ^ (M + 1)) ⧸ Ideal.span ({x} : Set _)) ≃ₐ[k]
      (MvPolynomial (Fin N) k ⧸ (RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin N) k →+* k)) ^ (M + 1))) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_nonempty_truncated_quotient_span_singleton_algEquiv_truncated_of_not_mem_sq.solution
