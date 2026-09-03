import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import P2M.Util
import P2M.Sol.S_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit
attribute [-instance] instTopologicallyFGOfFiniteType
set_option autoImplicit false

p2m_open "ModularCurve ModularCurve.UVCrossingModel~isIntegrallyClosed_of_uniformizer_pow_of_isAdicComplete"

theorem IsLocalRing.exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {W : Type*} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (π : W) (hπ : Irreducible π) (E : ℕ) (hE : 1 ≤ E)
    (θ : MvPowerSeries (Fin 2) W →+* AdicCompletion (IsLocalRing.maximalIdeal R) R)
    (hθ : Function.Surjective θ)
    (v : (AdicCompletion (IsLocalRing.maximalIdeal R) R)ˣ)
    (hrel : θ (MvPowerSeries.X 0) * θ (MvPowerSeries.X 1) =
      θ (MvPowerSeries.C π) ^ E * (v : AdicCompletion (IsLocalRing.maximalIdeal R) R))
    (hdim : 2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R)) :
    ∃ ι : AdicCompletion (IsLocalRing.maximalIdeal R) R ≃+* UVCrossingModel W (π ^ E),
      (∀ o : W, ι (θ (MvPowerSeries.C o)) = const (π ^ E) o) ∧
      ι (θ (MvPowerSeries.X 0)) = U (π ^ E) * ι (v : AdicCompletion (IsLocalRing.maximalIdeal R) R) ∧
      ι (θ (MvPowerSeries.X 1)) = V (π ^ E) := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_exists_ringEquiv_adicCompletion_uvCrossingModel_of_mul_eq_pow_mul_unit.solution
