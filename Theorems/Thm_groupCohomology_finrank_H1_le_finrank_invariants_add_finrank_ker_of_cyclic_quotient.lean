import Mathlib
import Definitions.Def_GroupCohomology_TateTwist
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_H1_le_finrank_invariants_add_finrank_ker_of_cyclic_quotient

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finrank_H1_le_finrank_invariants_add_finrank_ker_of_cyclic_quotient {k G : Type u} [Field k] [Group G] (A : Rep k G)
    [Finite G] [FiniteDimensional k A] (S : Subgroup G) [S.Normal] [Fintype (G ⧸ S)]
    (t : G) (ht : t ∈ S) (htS : S ≤ Subgroup.zpowers t)
    {φ : G} (hφ : ∀ x : G ⧸ S, x ∈ Subgroup.zpowers (QuotientGroup.mk φ : G ⧸ S))
    (m : ℕ) (hm : φ⁻¹ * t * φ = t ^ m)
    (hst : φ * t * φ⁻¹ ∈ Subgroup.zpowers t) :
    finrank k (groupCohomology.H1 A) ≤ finrank k A.ρ.invariants +
      finrank k (LinearMap.ker (m • groupCohomology.frobeniusOnCoinvariants A t φ hst - 1)) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_H1_le_finrank_invariants_add_finrank_ker_of_cyclic_quotient.solution
