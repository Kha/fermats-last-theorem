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
import P2M.Sol.S_NumberField_LevelArith_kummerChar_mul_and_add_and_level

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem NumberField.LevelArith.kummerChar_mul_and_add_and_level
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hζF : ζ ∈ F) :
    (∀ (x : (↥F)ˣ) (σ τ : ↥F.fixingSubgroup), kummerChar p ζ hζ F x (σ * τ) = kummerChar p ζ hζ F x σ + kummerChar p ζ hζ F x τ) ∧
    (∀ (x x' : (↥F)ˣ) (σ : ↥F.fixingSubgroup), kummerChar p ζ hζ F (x * x') σ = kummerChar p ζ hζ F x σ + kummerChar p ζ hζ F x' σ) ∧
    (∀ (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup),
      (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ (F ⊔ IntermediateField.adjoin ℚ {kummerRoot p F x}).fixingSubgroup → kummerChar p ζ hζ F x σ = 0) := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_kummerChar_mul_and_add_and_level.solution
