import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_finite_H2_units_and_natCard_le_of_isSolvable
attribute [-simp] IsLocalRing.principalUnits_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation.LocalLevel IsLocalRing groupCohomology
theorem ExtCitation.LocalLevel.finite_H2_units_and_natCard_le_of_isSolvable (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] (hsolv : Group.IsSolvable G) [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)) :
    Finite (groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) ∧
      Nat.card (groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) ≤ Nat.card G := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_finite_H2_units_and_natCard_le_of_isSolvable.solution
