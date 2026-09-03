import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_finiteDimensional_unitsModP_sClass_selmerRep

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith

theorem NumberField.LevelArith.finiteDimensional_unitsModP_sClass_selmerRep
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] :
    FiniteDimensional (ZMod p) (unitsModP K L hKL S p) ∧ FiniteDimensional (ZMod p) (sClassTorsionP K L hKL S p) ∧
      FiniteDimensional (ZMod p) (sClassModP K L hKL S p) ∧ FiniteDimensional (ZMod p) (selmerRep K L hKL S p) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_finiteDimensional_unitsModP_sClass_selmerRep.solution
