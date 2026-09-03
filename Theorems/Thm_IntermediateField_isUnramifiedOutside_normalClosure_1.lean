import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_IntermediateField_isUnramifiedOutside_normalClosure_1
set_option autoImplicit false

theorem IntermediateField.isUnramifiedOutside_normalClosure
    (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hF : F.IsUnramifiedOutside S) :
    F ≤ (normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ ∧
    FiniteDimensional ℚ ↥(normalClosure ℚ ↥F (AlgebraicClosure ℚ)) ∧
    IsGalois ℚ ↥(normalClosure ℚ ↥F (AlgebraicClosure ℚ)) ∧
    ((normalClosure ℚ ↥F (AlgebraicClosure ℚ)).restrictScalars ℚ).IsUnramifiedOutside S := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_isUnramifiedOutside_normalClosure_1.solution
