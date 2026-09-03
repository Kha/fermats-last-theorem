import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_range_infNatTrans_eq_of_unramified_level
attribute [-simp] IsLocalRing.principalUnits_zero

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.range_infNatTrans_eq_of_unramified_level (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ]
    (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L))
    (NL : Subgroup G) [NL.Normal] (hsolv : Group.IsSolvable (G ⧸ NL))
    (Nn : Subgroup G) [Nn.Normal] (hcard : Nat.card (G ⧸ Nn) = Nat.card (G ⧸ NL))
    (π : (↥L)ˣ) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖((π : L) : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ h ∈ Nn, h • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖((π : L) : PadicAlgCl q)‖) :
    LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ NL 2).app (Rep.ofMulDistribMulAction G (↥L)ˣ))) =
      LinearMap.range (ModuleCat.Hom.hom ((infNatTrans ℤ Nn 2).app (Rep.ofMulDistribMulAction G (↥L)ˣ))) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_range_infNatTrans_eq_of_unramified_level.solution
