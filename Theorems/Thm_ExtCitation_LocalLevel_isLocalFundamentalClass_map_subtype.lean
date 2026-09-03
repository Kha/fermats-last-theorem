import Mathlib
import Definitions.Def_ExtCitation_LocalLevel_FundamentalClass
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype
attribute [-simp] IsLocalRing.principalUnits_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.isLocalFundamentalClass_map_subtype (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (hsolv : Group.IsSolvable G)
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K] (hK : IsBase q L G K)
    (u : groupCohomology.H2 (Rep.ofMulDistribMulAction G (↥L)ˣ)) (hu : IsLocalFundamentalClass q L G K u)
    (S : Subgroup G) (KS : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] KS] (hKS : IsBase q L (↥S) KS) :
    IsLocalFundamentalClass q L (↥S) KS
      ((groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype (Rep.ofMulDistribMulAction G (↥L)ˣ))) 2).hom u) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_isLocalFundamentalClass_map_subtype.solution
