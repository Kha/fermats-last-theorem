import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_LocalRing_PrincipalUnits
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_exists_subgroup_units_forall_isMulCocycle

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open ExtCitation.LocalLevel IsLocalRing groupCohomology
theorem ExtCitation.LocalLevel.exists_subgroup_units_forall_isMulCocycle (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    [MulDistribMulAction G (↥L)ˣ] (hcompat : ∀ (g : G) (u : (↥L)ˣ), ((g • u : (↥L)ˣ) : L) = g • (u : L)) :
    ∃ U V : Subgroup (↥L)ˣ,
      (∀ u : (↥L)ˣ, u ∈ U ↔ ((u : L) ∈ Rw q L ∧ ((u⁻¹ : (↥L)ˣ) : L) ∈ Rw q L)) ∧
      (∀ g : G, ∀ u ∈ U, g • u ∈ U) ∧ V ≤ U ∧ (∀ g : G, ∀ v ∈ V, g • v ∈ V) ∧ (V.subgroupOf U).FiniteIndex ∧
      (∃ n : ℕ, 1 ≤ n ∧ ∀ u : (Rw q L)ˣ, u ∈ principalUnits (Rw q L) n →
          Units.map ((Rw q L).subtype : Rw q L →* L) u ∈ V) ∧
      (∀ f : G → (↥L)ˣ, (∀ g, f g ∈ V) → IsMulCocycle₁ f → ∃ x ∈ V, ∀ g, g • x / x = f g) ∧
      (∀ f : G × G → (↥L)ˣ, (∀ p, f p ∈ V) → IsMulCocycle₂ f →
          ∃ x : G → (↥L)ˣ, (∀ g, x g ∈ V) ∧ ∀ g h, g • x h / x (g * h) * x g = f (g, h)) := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_exists_subgroup_units_forall_isMulCocycle.solution
