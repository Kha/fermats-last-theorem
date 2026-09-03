import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Theorems.Thm_groupCohomology_locRes_extArithLoc_apply_mem_continuousH1
import P2M.Util
namespace P2MW.S_groupCohomology_locRes_mem_continuousH1_of_mem_continuousH1S

set_option autoImplicit false
open CategoryTheory Module groupCohomology ExtCitation

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (x : H1 M) (hx : x ∈ continuousH1S S M) (v : extArithIndex S) :
    (locRes (extArithLoc S) M v).hom x ∈ continuousH1 (extArithLoc S v) (Rep.res (extArithLoc S v) M) :=
  groupCohomology.locRes_extArithLoc_apply_mem_continuousH1 S M x (continuousH1S_le_continuousH1 S M hx) v
