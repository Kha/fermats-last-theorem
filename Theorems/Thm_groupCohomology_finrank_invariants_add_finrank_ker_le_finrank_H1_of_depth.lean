import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Definitions.Def_GroupCohomology_TateTwist
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth {k G : Type u} [Field k] [Group G] [Finite G] (A : Rep k G) [FiniteDimensional k A]
    (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)] (t : G) (ht : t ∈ S) (htS : S ≤ Subgroup.zpowers t)
    (φ : G) (hφ : ∀ x : G ⧸ S, x ∈ Subgroup.zpowers (QuotientGroup.mk φ : G ⧸ S))
    (m : ℕ) (hm : φ⁻¹ * t * φ = t ^ m) (hst : φ * t * φ⁻¹ ∈ Subgroup.zpowers t)
    (j : ℕ) (hrel : φ ^ orderOf (QuotientGroup.mk φ : G ⧸ S) = t ^ j)

    (hNt : ∑ i ∈ Finset.range (orderOf t), A.ρ (t ^ i) = 0)
    (hNj : ∑ i ∈ Finset.range j, A.ρ (t ^ i) = 0)
    (hNφ : ∑ i ∈ Finset.range (orderOf (QuotientGroup.mk φ : G ⧸ S)), A.ρ (φ ^ i) = 0)
    (hN : (A.quotientToInvariants S).ρ.norm = 0) :
    finrank k A.ρ.invariants
        + finrank k (LinearMap.ker (m • frobeniusOnCoinvariants A t φ hst - 1))
      ≤ finrank k (H1 A) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth.solution
