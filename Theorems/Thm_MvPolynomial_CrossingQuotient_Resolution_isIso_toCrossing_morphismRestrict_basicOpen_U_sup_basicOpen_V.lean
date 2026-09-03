import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

theorem MvPolynomial.CrossingQuotient.Resolution.isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V
    {W : Type u} [CommRing W] (t : W) {e : ℕ} (he : 0 < e) :
    Resolution.ι t e ⟨0, he⟩ ''ᵁ PrimeSpectrum.basicOpen (U t) =
        Resolution.toCrossing t e ⁻¹ᵁ PrimeSpectrum.basicOpen (U (t ^ e)) ∧
      Resolution.ι t e ⟨e - 1, Nat.sub_lt he Nat.one_pos⟩ ''ᵁ PrimeSpectrum.basicOpen (V t) =
        Resolution.toCrossing t e ⁻¹ᵁ PrimeSpectrum.basicOpen (V (t ^ e)) ∧
      IsIso (Resolution.toCrossing t e ∣_ PrimeSpectrum.basicOpen (U (t ^ e))) ∧
      IsIso (Resolution.toCrossing t e ∣_ PrimeSpectrum.basicOpen (V (t ^ e))) ∧
      IsIso (Resolution.toCrossing t e ∣_
        (PrimeSpectrum.basicOpen (U (t ^ e)) ⊔ PrimeSpectrum.basicOpen (V (t ^ e)))) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_isIso_toCrossing_morphismRestrict_basicOpen_U_sup_basicOpen_V.solution
