import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_exists_algEquiv_tensorProduct_apply_U_and_apply_V

set_option autoImplicit false

open MvPolynomial TensorProduct

universe u v

theorem MvPolynomial.CrossingQuotient.exists_algEquiv_tensorProduct_apply_U_and_apply_V
    (W : Type u) [CommRing W] (t : W) (B : Type u) [CommRing B] [Algebra W B] (b : B) (hb : algebraMap W B t = b) :
    ∃ e : CrossingQuotient B b ≃ₐ[B] B ⊗[W] CrossingQuotient W t,
      e (CrossingQuotient.U b) = (1 : B) ⊗ₜ[W] CrossingQuotient.U t ∧
      e (CrossingQuotient.V b) = (1 : B) ⊗ₜ[W] CrossingQuotient.V t := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_exists_algEquiv_tensorProduct_apply_U_and_apply_V.solution
