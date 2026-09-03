import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_nsmul_eq_zero_continuousH2Sr

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Module groupCohomology ExtCitation

theorem groupCohomology.exists_nsmul_eq_zero_continuousH2Sr
    {k : Type} [CommRing k] {G : Type} [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes) (M : Rep.{0} k G)
    (x : continuousH2Sr r S M) :
    ∃ n : ℕ, 0 < n ∧ n • x = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_nsmul_eq_zero_continuousH2Sr.solution
