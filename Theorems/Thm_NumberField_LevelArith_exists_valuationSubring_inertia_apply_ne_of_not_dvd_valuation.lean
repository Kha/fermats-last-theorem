import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_KummerCharacter
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem NumberField.LevelArith.exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation
    (p : ℕ) [Fact p.Prime] (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F]
    (x : (↥F)ˣ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F))
    (hw : ¬ (p : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero x))
    (y : AlgebraicClosure ℚ) (hy : y ^ p = ((x : ↥F) : AlgebraicClosure ℚ)) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), (∀ z : ↥F, (z : AlgebraicClosure ℚ) ∈ A ↔ w.valuation ↥F z ≤ 1) ∧
      ∃ σ ∈ A.inertiaSubgroupIn ℚ, (∀ z : ↥F, σ z = z) ∧ σ y ≠ y := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_valuationSubring_inertia_apply_ne_of_not_dvd_valuation.solution
