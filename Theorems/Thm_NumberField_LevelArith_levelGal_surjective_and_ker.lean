import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SUnitsMax
import P2M.Util
import P2M.Sol.S_NumberField_LevelArith_levelGal_surjective_and_ker

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology NumberField.LevelArith
open scoped NumberField.LevelArith

theorem NumberField.LevelArith.levelGal_surjective_and_ker
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)] :
    Function.Surjective (levelGal L F hLF) ∧ (levelGal L F hLF).ker = F.fixingSubgroup.comap L.fixingSubgroup.subtype := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_levelGal_surjective_and_ker.solution
