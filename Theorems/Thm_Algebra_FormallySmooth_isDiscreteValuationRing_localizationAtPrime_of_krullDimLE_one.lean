import Mathlib
import P2M.Util
import P2M.Sol.S_Algebra_FormallySmooth_isDiscreteValuationRing_localizationAtPrime_of_krullDimLE_one

set_option autoImplicit false

open IsLocalRing

theorem Algebra.FormallySmooth.isDiscreteValuationRing_localizationAtPrime_of_krullDimLE_one
    {k : Type} [Field k] {R : Type} [CommRing R] [IsDomain R] [Algebra k R]
    [Algebra.FormallySmooth k R] [Algebra.FinitePresentation k R] (hdim : Ring.KrullDimLE 1 R)
    (𝔫 : Ideal R) [𝔫.IsMaximal] (hne : 𝔫 ≠ ⊥)
    (hrat : Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap k R))) :
    ∃ _ : IsDomain (Localization.AtPrime 𝔫), IsDiscreteValuationRing (Localization.AtPrime 𝔫) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_FormallySmooth_isDiscreteValuationRing_localizationAtPrime_of_krullDimLE_one.solution
