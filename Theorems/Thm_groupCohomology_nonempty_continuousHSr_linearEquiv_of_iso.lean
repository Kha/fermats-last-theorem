import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import P2M.Util
import P2M.Sol.S_groupCohomology_nonempty_continuousHSr_linearEquiv_of_iso

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation
open scoped Classical

theorem groupCohomology.nonempty_continuousHSr_linearEquiv_of_iso
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    {A B : Rep.{0} (ZMod p) ↥K.fixingSubgroup} (e : A ≅ B) :
    Nonempty (↥(continuousH1Sr K.fixingSubgroup.subtype S A) ≃ₗ[ZMod p] ↥(continuousH1Sr K.fixingSubgroup.subtype S B)) ∧
      Nonempty (continuousH2Sr K.fixingSubgroup.subtype S A ≃ₗ[ZMod p] continuousH2Sr K.fixingSubgroup.subtype S B) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_nonempty_continuousHSr_linearEquiv_of_iso.solution
