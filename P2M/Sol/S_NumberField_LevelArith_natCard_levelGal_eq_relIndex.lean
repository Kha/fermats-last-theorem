import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import P2M.Util
namespace P2MW.S_NumberField_LevelArith_natCard_levelGal_eq_relIndex

set_option autoImplicit false
open NumberField.LevelArith
open scoped NumberField.LevelArith

namespace L3XCard

local instance isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

theorem surjective (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] :
    Function.Surjective (levelGal K L hKL) := by
  haveI : Normal ↥K (AlgebraicClosure ℚ) := Normal.tower_top_of_normal ℚ ↥K (AlgebraicClosure ℚ)
  intro τ
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥(levelField K L hKL)) (AlgebraicClosure ℚ) τ
  exact ⟨(IntermediateField.fixingSubgroupEquiv K).symm σ, by
    change AlgEquiv.restrictNormalHom _ ((IntermediateField.fixingSubgroupEquiv K) ((IntermediateField.fixingSubgroupEquiv K).symm σ)) = τ
    rw [MulEquiv.apply_symm_apply, hσ]⟩

theorem mem_ker_iff (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] (γ : ↥K.fixingSubgroup) :
    γ ∈ (levelGal K L hKL).ker ↔ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup := by
  rw [MonoidHom.mem_ker]
  refine ⟨fun h => ?_, levelGal_eq_one_of_mem K L hKL γ⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have := congrArg (fun φ => ((φ ⟨x, (IntermediateField.mem_extendScalars hKL).2 hx⟩ : ↥(levelField K L hKL)) : AlgebraicClosure ℚ)) h
  simpa [levelGal_apply_coe] using this

end L3XCard

theorem solution
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)] :
    Nat.card (LevelGal K L hKL) = L.fixingSubgroup.relIndex K.fixingSubgroup := by
  have hker : (levelGal K L hKL).ker = L.fixingSubgroup.subgroupOf K.fixingSubgroup :=
    Subgroup.ext fun γ => by rw [L3XCard.mem_ker_iff, Subgroup.mem_subgroupOf]
  have hrange : (levelGal K L hKL).range = ⊤ := MonoidHom.range_eq_top.2 (L3XCard.surjective K L hKL)
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker, hrange, Subgroup.card_top]
