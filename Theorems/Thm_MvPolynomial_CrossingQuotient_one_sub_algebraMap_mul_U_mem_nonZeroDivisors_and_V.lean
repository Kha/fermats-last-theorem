import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolution
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_one_sub_algebraMap_mul_U_mem_nonZeroDivisors_and_V

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.one_sub_algebraMap_mul_U_mem_nonZeroDivisors_and_V
    {W : Type*} [CommRing W] (t : W) (ht : t ∈ nonZeroDivisors W) (w : W) :
    1 - algebraMap W (CrossingQuotient W t) w * U t ∈ nonZeroDivisors (CrossingQuotient W t) ∧
      1 - algebraMap W (CrossingQuotient W t) w * V t ∈ nonZeroDivisors (CrossingQuotient W t) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_one_sub_algebraMap_mul_U_mem_nonZeroDivisors_and_V.solution
