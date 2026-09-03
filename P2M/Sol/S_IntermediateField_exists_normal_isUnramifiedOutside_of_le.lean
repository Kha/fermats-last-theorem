import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import P2M.Util
namespace P2MW.S_IntermediateField_exists_normal_isUnramifiedOutside_of_le

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), F ≤ L ∧ L.IsUnramifiedOutside S ∧ Normal ℚ L := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  exact ⟨IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ), IntermediateField.le_normalClosure F, hF.normalClosure, normalClosure.normal ℚ F (AlgebraicClosure ℚ)⟩
