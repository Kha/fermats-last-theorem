import Mathlib
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_fixedLevel_quotientToInvariants_iso

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open groupCohomology
theorem ExtCitation.LocalLevel.exists_fixedLevel_quotientToInvariants_iso (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (N : Subgroup G) [N.Normal] :
    ∃ (L' : IntermediateField ℚ_[q] (PadicAlgCl q)) (_ : FiniteDimensional ℚ_[q] L')
      (_ : MulSemiringAction (G ⧸ N) L') (_ : FaithfulSMul (G ⧸ N) L')
      (_ : MulDistribMulAction (G ⧸ N) (↥L')ˣ),
      (∀ (g : G ⧸ N) (x : ℚ_[q]), g • algebraMap ℚ_[q] L' x = algebraMap ℚ_[q] L' x) ∧
      (∀ (g : G ⧸ N) (u : (↥L')ˣ), ((g • u : (↥L')ˣ) : L') = g • (u : L')) ∧
      Nonempty ((Rep.ofMulDistribMulAction G (↥L)ˣ).quotientToInvariants N ≅
        Rep.ofMulDistribMulAction (G ⧸ N) (↥L')ˣ) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_fixedLevel_quotientToInvariants_iso.solution
