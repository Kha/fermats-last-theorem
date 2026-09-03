import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import P2M.Util
namespace P2MW.S_IntermediateField_isUnramifiedOutside_normalClosure_1
set_option autoImplicit false

open IntermediateField in

theorem solution
    (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hF : F.IsUnramifiedOutside S) :
    F ≤ (normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ ∧
    FiniteDimensional ℚ ↥(normalClosure ℚ ↥F (AlgebraicClosure ℚ)) ∧
    IsGalois ℚ ↥(normalClosure ℚ ↥F (AlgebraicClosure ℚ)) ∧
    ((normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ).IsUnramifiedOutside S := by
  haveI : FiniteDimensional ℚ ↥F := hF.1
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.instIsAlgClosure ℚ; rfl; rfl
  haveI : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ _
  have hle : F ≤ (normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ := fun x hx =>
    (IntermediateField.mem_restrictScalars ℚ).2 (IntermediateField.le_normalClosure F hx)
  have hle' : (normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ ≤ normalClosure ℚ ↥F (AlgebraicClosure ℚ) :=
    fun x hx => (IntermediateField.mem_restrictScalars ℚ).1 hx
  exact ⟨hle, normalClosure.is_finiteDimensional ℚ ↥F (AlgebraicClosure ℚ), IsGalois.normalClosure ℚ ↥F (AlgebraicClosure ℚ),
    hF.normalClosure.of_le hle'⟩
