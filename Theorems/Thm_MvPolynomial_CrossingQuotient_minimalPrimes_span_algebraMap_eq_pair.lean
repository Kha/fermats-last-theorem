import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_minimalPrimes_span_algebraMap_eq_pair

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.minimalPrimes_span_algebraMap_eq_pair
    {W : Type*} [CommRing W] (t : W) [IsDomain (W ⧸ Ideal.span {t})] :
    (Ideal.span {algebraMap W (CrossingQuotient W t) t}).minimalPrimes =
        {Ideal.span {U t}, Ideal.span {V t}} ∧
    Ideal.span {U t} ≠ Ideal.span {V t} := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_minimalPrimes_span_algebraMap_eq_pair.solution
