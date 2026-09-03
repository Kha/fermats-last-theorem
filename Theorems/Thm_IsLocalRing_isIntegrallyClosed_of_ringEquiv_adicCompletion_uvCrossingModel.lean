import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel
set_option autoImplicit false

open ModularCurve

theorem IsLocalRing.isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (ι : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* UVCrossingModel W (π ^ E)) :
    IsIntegrallyClosed R := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_isIntegrallyClosed_of_ringEquiv_adicCompletion_uvCrossingModel.solution
