import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_PlaceTransport
import P2M.Util
import P2M.Sol.S_NumberField_exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one
attribute [-instance] AlgebraicClosure.Rat.isGalois

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
p2m_open "scoped Classical NumberField.LevelArith NumberField.PlaceTransport NumberField~exists_valuationSubring_eq_localization Pointwise"

theorem NumberField.exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥F)) :
    ∃ B : ValuationSubring (AlgebraicClosure ℚ), ∀ x : ↥F, (x : AlgebraicClosure ℚ) ∈ B ↔ v.valuation ↥F x ≤ 1 := by p2m_exact_reverting @_root_.P2MW.S_NumberField_exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one.solution
