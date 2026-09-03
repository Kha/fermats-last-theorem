import Mathlib
import Definitions.Def_GroupCohomology_TateTwist
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_ker_le_finrank_ker_frobeniusOnCoinvariants_of_model

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finrank_ker_le_finrank_ker_frobeniusOnCoinvariants_of_model
    {k G : Type u} [Field k] [Group G] (M : Rep k G) [FiniteDimensional k M]
    (U W : Subgroup G) [U.Normal] [W.Normal] [U.FiniteIndex] [W.FiniteIndex]
    (hU : ∀ u ∈ U, M.ρ u = 1)
    (q : ℕ) [Fact q.Prime] (hq : (q : k) ≠ 0) (hW : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U)
    (t φ : G)
    (hst : (QuotientGroup.mk φ : G ⧸ W) * QuotientGroup.mk t * (QuotientGroup.mk φ)⁻¹
      ∈ Subgroup.zpowers (QuotientGroup.mk t : G ⧸ W))
    (D : Type u) [AddCommGroup D] [Module k D] [FiniteDimensional k D]
    (π : M →ₗ[k] D)
    (hker : LinearMap.ker π ≤ (⨆ w ∈ W, LinearMap.range (M.ρ w - 1)) ⊔ LinearMap.range (M.ρ t - 1))
    (hπt : LinearMap.range (M.ρ t - 1) ≤ LinearMap.ker π)
    (hπ : Function.Surjective π)
    (hkerW : (⨆ w ∈ W, LinearMap.range (M.ρ w - 1)) ≤ LinearMap.ker π)
    (φD : D →ₗ[k] D) (hφD : φD ∘ₗ π = π ∘ₗ M.ρ φ)
    (m : ℕ) (b : k) (hmb : (m : k) * b = 1) :
    finrank k (LinearMap.ker (φD - b • 1))
      ≤ finrank k (LinearMap.ker (m • frobeniusOnCoinvariants (M.quotientToInvariants W)
        (QuotientGroup.mk t) (QuotientGroup.mk φ) hst - 1)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_ker_le_finrank_ker_frobeniusOnCoinvariants_of_model.solution
