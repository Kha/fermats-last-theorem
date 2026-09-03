import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_exists_algEquiv_quotient_span_U_and_span_V_polynomial

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.exists_algEquiv_quotient_span_U_and_span_V_polynomial
    {W : Type*} [CommRing W] (t : W) :
    (∃ E : (CrossingQuotient W t ⧸ Ideal.span {U t}) ≃ₐ[W] Polynomial (W ⧸ Ideal.span {t}),
        E (Ideal.Quotient.mk (Ideal.span {U t}) (V t)) = Polynomial.X) ∧
    (∃ E : (CrossingQuotient W t ⧸ Ideal.span {V t}) ≃ₐ[W] Polynomial (W ⧸ Ideal.span {t}),
        E (Ideal.Quotient.mk (Ideal.span {V t}) (U t)) = Polynomial.X) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_exists_algEquiv_quotient_span_U_and_span_V_polynomial.solution
