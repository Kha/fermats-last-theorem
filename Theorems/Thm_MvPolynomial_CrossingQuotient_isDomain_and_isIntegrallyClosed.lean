import Mathlib
import Definitions.Def_MvPolynomial_CrossingQuotient
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_isDomain_and_isIntegrallyClosed

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.isDomain_and_isIntegrallyClosed
    {W : Type*} [CommRing W] [IsDomain W] [UniqueFactorizationMonoid W] (t : W) (ht : t ≠ 0) :
    IsDomain (MvPolynomial.CrossingQuotient W t) ∧
      IsIntegrallyClosed (MvPolynomial.CrossingQuotient W t) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_isDomain_and_isIntegrallyClosed.solution
