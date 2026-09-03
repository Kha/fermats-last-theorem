import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_isRegularLocalRing_stalk

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.Resolution.isRegularLocalRing_stalk
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) (x : Resolution ϖ e) :
    IsRegularLocalRing ((Resolution ϖ e).presheaf.stalk x) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isRegularLocalRing_stalk.solution
