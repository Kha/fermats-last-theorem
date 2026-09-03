import Mathlib
import Definitions.Def_MvPolynomial_CrossingQuotient
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_ringKrullDim_le

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

theorem MvPolynomial.CrossingQuotient.ringKrullDim_le
    (W : Type u) [CommRing W] [IsDomain W] [IsNoetherianRing W] (n : ℕ) (hW : ringKrullDim W = n)
    (t : W) (ht : t ≠ 0) :
    ringKrullDim (CrossingQuotient W t) ≤ n + 1 := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_ringKrullDim_le.solution
