import Mathlib
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_GroupCohomology_CyclicCarry
import P2M.Util
import P2M.Sol.S_ExtCitation_LocalLevel_mem_adjoin_rootsOfUnity_of_forall_inf_smul_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation.LocalLevel

theorem ExtCitation.LocalLevel.mem_adjoin_rootsOfUnity_of_forall_inf_smul_eq (q : ℕ) [Fact q.Prime]
    (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
    (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
    (S : Subgroup G)
    (K' : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K'] (hK'L : K' ≤ L)
    (hK' : ∀ x : L, (x : PadicAlgCl q) ∈ K' ↔ ∀ s ∈ S, s • x = x)
    (N : Subgroup G) [N.Normal]
    (π : L) (hπG : ∀ g : G, g • π = π) (hπ1 : ‖(π : PadicAlgCl q)‖ < 1)
    (hπmax : ∀ y : L, (∀ n ∈ N, n • y = y) → ‖(y : PadicAlgCl q)‖ < 1 → ‖(y : PadicAlgCl q)‖ ≤ ‖(π : PadicAlgCl q)‖) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ x : L, (∀ n ∈ N ⊓ S, n • x = x) →
      (x : PadicAlgCl q) ∈ IntermediateField.adjoin K' {ζ : PadicAlgCl q | ζ ^ (q ^ N₀ - 1) = 1} := by p2m_exact_reverting @_root_.P2MW.S_ExtCitation_LocalLevel_mem_adjoin_rootsOfUnity_of_forall_inf_smul_eq.solution
