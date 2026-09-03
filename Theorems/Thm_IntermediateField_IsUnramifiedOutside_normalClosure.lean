import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import P2M.Util
import P2M.Sol.S_IntermediateField_IsUnramifiedOutside_normalClosure

set_option autoImplicit false
theorem IntermediateField.IsUnramifiedOutside.normalClosure
    {S : Finset Nat.Primes} {F : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) :
    (IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)).IsUnramifiedOutside S := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_IsUnramifiedOutside_normalClosure.solution
