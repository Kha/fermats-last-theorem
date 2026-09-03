import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.isZero_groupCohomology_one_res_units (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (Γ : Type) [Group Γ] (f : Γ →* G) (hf : Function.Injective f) :
    CategoryTheory.Limits.IsZero (groupCohomology (Rep.res f (Rep.ofMulDistribMulAction G (↥L)ˣ)) 1) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_isZero_groupCohomology_one_res_units.solution
