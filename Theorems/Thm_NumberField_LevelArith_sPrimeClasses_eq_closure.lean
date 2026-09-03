import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_sPrimeClasses_eq_closure

set_option autoImplicit false
open NumberField.LevelArith
open scoped NumberField.LevelArith

theorem NumberField.LevelArith.sPrimeClasses_eq_closure
    (E F : Type) [Field E] [Field F] [NumberField F] [Algebra E F] (S : Set Nat.Primes) :
    sPrimeClasses E F S = Subgroup.closure (primeClass F '' placesOverPrimes F S) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_sPrimeClasses_eq_closure.solution
