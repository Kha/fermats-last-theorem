import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_IntermediateField_exists_normal_isUnramifiedOutside_of_le

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem IntermediateField.exists_normal_isUnramifiedOutside_of_le
    (S : Finset Nat.Primes) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : F.IsUnramifiedOutside S) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), F ≤ L ∧ L.IsUnramifiedOutside S ∧ Normal ℚ L := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_exists_normal_isUnramifiedOutside_of_le.solution
