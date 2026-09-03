import Theorems.Thm_FrobeniusDensity_degOneSum_add_log_isBigO
import Theorems.Thm_FrobeniusDensity_summable_degOne_term
import Definitions.Def_FrobeniusDensity_DegOneAsymptotic
import P2M.Util
namespace P2MW.S_FrobeniusDensity_degOneAsymptotic

set_option autoImplicit false

open NumberField

theorem solution (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L] :
    FrobeniusDensity.DegOneAsymptotic L := fun H S₀ =>
  ⟨fun _ hs => FrobeniusDensity.summable_degOne_term
      (FixedPoints.intermediateField H : IntermediateField ℚ L) S₀ hs,
    FrobeniusDensity.degOneSum_add_log_isBigO
      (FixedPoints.intermediateField H : IntermediateField ℚ L) S₀⟩
