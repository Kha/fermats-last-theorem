import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_existsUnique_ringHom_comp_algebraMap_eq_and_apply_U_eq_and_apply_V_eq

set_option autoImplicit false

open MvPolynomial

theorem MvPolynomial.CrossingQuotient.existsUnique_ringHom_comp_algebraMap_eq_and_apply_U_eq_and_apply_V_eq
    {W : Type*} [CommRing W] {S : Type*} [CommRing S] (ι : W →+* S) (t : W) (x y : S)
    (hxy : x * y = ι t) :
    ∃! χ : CrossingQuotient W t →+* S,
      χ.comp (algebraMap W (CrossingQuotient W t)) = ι ∧ χ (CrossingQuotient.U t) = x ∧ χ (CrossingQuotient.V t) = y := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_existsUnique_ringHom_comp_algebraMap_eq_and_apply_U_eq_and_apply_V_eq.solution
