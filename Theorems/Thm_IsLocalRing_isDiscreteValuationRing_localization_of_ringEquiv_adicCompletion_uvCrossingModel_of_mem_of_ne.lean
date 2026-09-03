import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_isDiscreteValuationRing_localization_of_ringEquiv_adicCompletion_uvCrossingModel_of_mem_of_ne
attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

p2m_open "IsLocalRing~isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel ModularCurve ModularCurve.UVCrossingModel~two_le_ringKrullDim"

theorem IsLocalRing.isDiscreteValuationRing_localization_of_ringEquiv_adicCompletion_uvCrossingModel_of_mem_of_ne
    {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (maximalIdeal R) R ≃+* UVCrossingModel W (π ^ E))
    (ϖ : R) (hϖ : ι (algebraMap R (AdicCompletion (maximalIdeal R) R) ϖ) = const (π ^ E) π)
    (Q : Ideal R) [Q.IsPrime] (hϖQ : ϖ ∈ Q) (hQ : Q ≠ maximalIdeal R) :
    IsDiscreteValuationRing (Localization.AtPrime Q) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isDiscreteValuationRing_localization_of_ringEquiv_adicCompletion_uvCrossingModel_of_mem_of_ne.solution
