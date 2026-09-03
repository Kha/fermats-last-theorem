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
import P2M.Sol.S_NumberField_LevelArith_exists_kummerChar_eq_of_continuous
attribute [-instance] groupCohomology.Kummer.instMulDistribMulActionRootsOfUnity
attribute [-simp] groupCohomology.Kummer.coe_kummerCocycleRoots groupCohomology.Kummer.mem_powerSubgroup_iff groupCohomology.Kummer.val_smul_units groupCohomology.Kummer.kummerHom_apply groupCohomology.Kummer.coe_smul_rootsOfUnity

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain
open scoped Classical NumberField NumberField.LevelArith

theorem NumberField.LevelArith.exists_kummerChar_eq_of_continuous
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F] (hζF : ζ ∈ F)
    (χ : ↥F.fixingSubgroup → ZMod p) (hχ : ∀ σ τ : ↥F.fixingSubgroup, χ (σ * τ) = χ σ + χ τ)
    (F₀ : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥F₀] (hF₀ : F ≤ F₀)
    (hχ₀ : ∀ σ : ↥F.fixingSubgroup, (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ F₀.fixingSubgroup → χ σ = 0) :
    ∃ x : (↥F)ˣ, ∀ σ : ↥F.fixingSubgroup, kummerChar p ζ hζ F x σ = χ σ := by p2m_exact_reverting @_root_.P2MW.S_NumberField_LevelArith_exists_kummerChar_eq_of_continuous.solution
