import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import P2M.Util
import P2M.Sol.S_groupCohomology_locRes_mem_continuousH1_of_mem_continuousH1S

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation
theorem groupCohomology.locRes_mem_continuousH1_of_mem_continuousH1S
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (x : H1 M) (hx : x ∈ continuousH1S S M) (v : extArithIndex S) :
    (locRes (extArithLoc S) M v).hom x ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_locRes_mem_continuousH1_of_mem_continuousH1S.solution
