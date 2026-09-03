import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import P2M.Util
import P2M.Sol.S_MvPolynomial_CrossingQuotient_Resolution_eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient~minimalPrimes_span_algebraMap_eq_pair"

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen
    {O : Type u} [CommRing O] (ϖ : O) (e : ℕ) [IsDomain (O ⧸ Ideal.span {ϖ})] (k : Fin e)
    (P : chartScheme ϖ) (hP : P.asIdeal = Ideal.span {U ϖ} ∨ P.asIdeal = Ideal.span {V ϖ})
    (o : Resolution ϖ e) (ho : o ⤳ Resolution.ι ϖ e k P)
    (hoϖ : o ∉ Resolution.toSpec ϖ e ⁻¹ᵁ (PrimeSpectrum.basicOpen ϖ : (Spec (CommRingCat.of O)).Opens)) :
    o = Resolution.ι ϖ e k P := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_CrossingQuotient_Resolution_eq_iota_apply_of_specializes_of_notMem_preimage_basicOpen.solution
