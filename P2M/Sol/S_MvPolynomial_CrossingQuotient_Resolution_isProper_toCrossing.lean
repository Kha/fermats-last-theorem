import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_isSeparated
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_locallyOfFiniteType_and_quasiCompact_toCrossing
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_valuativeCriterion_existence_toCrossing
import P2M.Util
namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isProper_toCrossing

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

namespace CrossingResolutionL6Proper

theorem main {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    IsProper (Resolution.toCrossing t e) := by
  obtain ⟨-, hsep⟩ := Resolution.isSeparated t e
  obtain ⟨hft, hqc⟩ := Resolution.locallyOfFiniteType_and_quasiCompact_toCrossing t e
  have huc : UniversallyClosed (Resolution.toCrossing t e) :=
    UniversallyClosed.of_valuativeCriterion _
      (Resolution.valuativeCriterion_existence_toCrossing t e)
  exact IsProper.mk

end CrossingResolutionL6Proper

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient in
theorem solution
    {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    IsProper (Resolution.toCrossing t e) :=
  CrossingResolutionL6Proper.main t e
