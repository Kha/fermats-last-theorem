import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors

set_option autoImplicit false

p2m_open "MvPolynomial MvPolynomial.CrossingQuotient~linearIndependent_monomial_and_span_eq_top"

theorem MvPolynomial.CrossingQuotient.U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors
    {W : Type*} [CommRing W] (t : W) (ht : t ∈ nonZeroDivisors W) :
    U t ∈ nonZeroDivisors (CrossingQuotient W t) ∧ V t ∈ nonZeroDivisors (CrossingQuotient W t) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_U_mem_nonZeroDivisors_and_V_mem_nonZeroDivisors.solution
