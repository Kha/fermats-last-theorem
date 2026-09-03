import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_natCard_levelGal_eq_relIndex

set_option autoImplicit false
open NumberField.LevelArith
open scoped NumberField.LevelArith

theorem NumberField.LevelArith.natCard_levelGal_eq_relIndex
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] :
    Nat.card (LevelGal K L hKL) = L.fixingSubgroup.relIndex K.fixingSubgroup := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_natCard_levelGal_eq_relIndex.solution
