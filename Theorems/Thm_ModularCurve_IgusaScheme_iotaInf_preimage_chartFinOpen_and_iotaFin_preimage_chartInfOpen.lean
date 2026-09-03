import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme
namespace ModularCurve.IgusaScheme

theorem iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    ιInf N ℓ ⁻¹ᵁ chartFinOpen N ℓ = PrimeSpectrum.basicOpen (jInvChartInf N ℓ) ∧
    ιFin N ℓ ⁻¹ᵁ chartInfOpen N ℓ = PrimeSpectrum.basicOpen (jChartFin N ℓ) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_iotaInf_preimage_chartFinOpen_and_iotaFin_preimage_chartInfOpen.solution

end ModularCurve.IgusaScheme
