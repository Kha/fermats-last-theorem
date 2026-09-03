import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_locallyOfFiniteType_and_quasiCompact_toCrossing

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.Resolution.locallyOfFiniteType_and_quasiCompact_toCrossing
    {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    LocallyOfFiniteType (Resolution.toCrossing t e) ∧ QuasiCompact (Resolution.toCrossing t e) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_locallyOfFiniteType_and_quasiCompact_toCrossing.solution
