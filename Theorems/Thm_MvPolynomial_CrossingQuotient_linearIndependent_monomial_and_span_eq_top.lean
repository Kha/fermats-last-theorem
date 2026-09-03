import Mathlib
import Definitions.Def_MvPolynomial_CrossingQuotient
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient
theorem MvPolynomial.CrossingQuotient.linearIndependent_monomial_and_span_eq_top
    {W : Type*} [CommRing W] (t : W) :
    LinearIndependent W (MvPolynomial.CrossingQuotient.monomial t) ∧
      Submodule.span W (Set.range (MvPolynomial.CrossingQuotient.monomial t)) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top.solution
