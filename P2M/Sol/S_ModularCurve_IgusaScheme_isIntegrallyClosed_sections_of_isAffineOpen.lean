import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_sections_of_isAffineOpen
import P2M.Util
namespace P2MW.S_ModularCurve_IgusaScheme_isIntegrallyClosed_sections_of_isAffineOpen

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.IgusaScheme

theorem solution (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (U : (ModularCurve.IgusaScheme N ℓ).Opens) (hU : IsAffineOpen U) :
    IsIntegrallyClosed ↑Γ(ModularCurve.IgusaScheme N ℓ, U) :=
  AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_sections_of_isAffineOpen
    (↥(GaloisRep.ratLocalizedAt ℓ)) (↥(modularFunctionFieldFull N)) (jFull N) U hU
