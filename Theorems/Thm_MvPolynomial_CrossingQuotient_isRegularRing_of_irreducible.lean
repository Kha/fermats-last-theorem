import Mathlib
import Definitions.Def_MvPolynomial_CrossingQuotient
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_isRegularRing_of_irreducible

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.isRegularRing_of_irreducible
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) :
    IsRegularRing (CrossingQuotient R ϖ) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_isRegularRing_of_irreducible.solution
