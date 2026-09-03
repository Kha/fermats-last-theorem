import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import P2M.Util
import P2M.Sol.S_ModularCurve_IgusaScheme_forall_mem_asIdeal_iff_mem_nonunits_of_iotaFin_eq_of_iotaInf_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve

theorem ModularCurve.IgusaScheme.forall_mem_asIdeal_iff_mem_nonunits_of_iotaFin_eq_of_iotaInf_eq
    (M ℓ : ℕ) [NeZero M] [Fact ℓ.Prime]
    (𝔮 : PrimeSpectrum ↥(IgusaScheme.chartAlgFin M ℓ)) (𝔯 : PrimeSpectrum ↥(IgusaScheme.chartAlgInf M ℓ))
    (h : (IgusaScheme.ιFin M ℓ).base 𝔮 = (IgusaScheme.ιInf M ℓ).base 𝔯)
    (V : ValuationSubring ↥(modularFunctionFieldFull M))

    (hAV : ∀ b : ↥(IgusaScheme.chartAlgInf M ℓ), ((b : ↥(modularFunctionFieldFull M)) ∈ V))
    (hV : ∀ b : ↥(IgusaScheme.chartAlgInf M ℓ), b ∈ 𝔯.asIdeal ↔ ((b : ↥(modularFunctionFieldFull M)) ∈ V.nonunits)) :
    ∀ a : ↥(IgusaScheme.chartAlgFin M ℓ), a ∈ 𝔮.asIdeal ↔ ((a : ↥(modularFunctionFieldFull M)) ∈ V.nonunits) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_IgusaScheme_forall_mem_asIdeal_iff_mem_nonunits_of_iotaFin_eq_of_iotaInf_eq.solution
