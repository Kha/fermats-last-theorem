import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_IntermediateField_adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow
attribute [-instance] WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy
attribute [-simp] WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation
theorem IntermediateField.adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (k : ℕ)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) :
    (IntermediateField.adjoin ℚ ({ζ} : Set (AlgebraicClosure ℚ))).IsUnramifiedOutside S := by p2m_exact_reverting @_root_.P2MW.S_IntermediateField_adjoin_isUnramifiedOutside_of_isPrimitiveRoot_pow.solution
