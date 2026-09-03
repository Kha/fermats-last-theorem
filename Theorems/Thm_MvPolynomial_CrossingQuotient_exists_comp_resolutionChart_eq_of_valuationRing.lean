import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_exists_comp_resolutionChart_eq_of_valuationRing

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.exists_comp_resolutionChart_eq_of_valuationRing
    {W : Type*} [CommRing W] (t : W) {e : ℕ} (he : 0 < e)
    {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O]
    (g : CrossingQuotient W (t ^ e) →+* O) :
    ∃ (i : Fin e) (g' : CrossingQuotient W t →+* O),
      g'.comp (resolutionChart t e i).toRingHom = g := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_exists_comp_resolutionChart_eq_of_valuationRing.solution
