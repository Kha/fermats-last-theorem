import Mathlib
import Definitions.Def_GroupCohomology_TangentSpace
import P2M.Util
import P2M.Sol.S_groupCohomology_dualLiftToCochain_sub_mem_oneCoboundaries_iff

universe u

open scoped DualNumber RightActions
open TrivSqZeroExt groupCohomology
theorem groupCohomology.dualLiftToCochain_sub_mem_oneCoboundaries_iff
    {k A G : Type u} [CommRing k] [Ring A] [Algebra k A] [Group G]
    {ρ₀ : G →* Aˣ} {ρ ρ' : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ) (hρ' : IsDualLift ρ₀ ρ') :
    dualLiftToCochain ρ₀ ρ - dualLiftToCochain ρ₀ ρ' ∈ coboundaries₁ (adjointRep k ρ₀)
      ↔ ∃ w : (A[ε])ˣ, (w : A[ε]).fst = 1 ∧ ∀ g, ρ' g = w * ρ g * w⁻¹ := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_dualLiftToCochain_sub_mem_oneCoboundaries_iff.solution
