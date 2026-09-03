import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem

set_option autoImplicit false

universe u v

theorem MvPolynomial.exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem
    (R : Type u) [CommRing R] (N : ℕ) (f : Fin N → MvPolynomial (Fin N) R)
    (e : MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range f)) (he : IsIdempotentElem e) :
    ∃ f' : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R,
      Nonempty ((MvPolynomial (Fin (N + 1)) R ⧸ Ideal.span (Set.range f')) ≃ₐ[R]
        ((MvPolynomial (Fin N) R ⧸ Ideal.span (Set.range f)) ⧸ Ideal.span {e})) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_exists_quotient_span_quotient_span_singleton_algEquiv_of_isIdempotentElem.solution
