import Mathlib
import Definitions.Def_NumberField_LevelArithmeticModP
import P2M.Util
namespace P2MW.S_NumberField_LevelArith_isGalois_levelField

set_option autoImplicit false
open NumberField.LevelArith
open scoped NumberField.LevelArith

theorem solution
    (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] :
    IsGalois ↥L ↥(levelField L F hLF) := by

  haveI : IsGalois ℚ ↥F := IsGalois.mk

  haveI : IsGalois ℚ ↥(levelField L F hLF) := ‹IsGalois ℚ ↥F›
  exact IsGalois.tower_top_of_isGalois ℚ ↥L ↥(levelField L F hLF)
