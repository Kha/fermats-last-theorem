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
import P2M.Sol.S_NumberField_LevelArith_kummerChar_conj_eq_cycloChar_mul

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem NumberField.LevelArith.kummerChar_conj_eq_cycloChar_mul
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hζF : ζ ∈ F)
    (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (hγF : ∀ z ∈ F, γ z ∈ F)
    (σ : ↥F.fixingSubgroup) (hconj : γ * (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * γ⁻¹ ∈ F.fixingSubgroup)
    (x x' : (↥F)ˣ) (hx' : ((x' : ↥F) : AlgebraicClosure ℚ) = γ ((x : ↥F) : AlgebraicClosure ℚ)) :
    kummerChar p ζ hζ F x' ⟨γ * (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * γ⁻¹, hconj⟩ = ((cycloChar p γ : ZMod p)) * kummerChar p ζ hζ F x σ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_kummerChar_conj_eq_cycloChar_mul.solution
