import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_LevelArithmeticModP
import Theorems.Thm_NumberField_LevelArith_levelGal_surjective_and_ker
import P2M.Util
namespace P2MW.S_NumberField_LevelArith_isPGroup_levelGal_of_isPGroup_quotient

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology ExtCitation NumberField IsDedekindDomain NumberField.LevelArith
open scoped NumberField.LevelArith

theorem solution
    (p : ℕ) [Fact p.Prime] (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)]
    (hG : IsPGroup p (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
    IsPGroup p (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) := by
  obtain ⟨hsurj, hker⟩ := NumberField.LevelArith.levelGal_surjective_and_ker L F hLF
  refine hG.of_surjective (QuotientGroup.lift _ (levelGal L F hLF) (le_of_eq hker.symm)) ?_
  intro y
  obtain ⟨γ, rfl⟩ := hsurj y
  exact ⟨QuotientGroup.mk γ, rfl⟩
