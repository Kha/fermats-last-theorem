import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_GroupCohomology_TateTwist
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_inflationImage_le_finrank_invariants_add_finrank_invariants_dualTwist

set_option autoImplicit false
open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finrank_inflationImage_le_finrank_invariants_add_finrank_invariants_dualTwist
    {k G : Type u} [Field k] [Group G] (M : Rep k G) [FiniteDimensional k M]
    (χ : G →* kˣ)
    (U W I : Subgroup G) [U.Normal] [W.Normal] [I.Normal] [U.FiniteIndex] [W.FiniteIndex]
    (hU : ∀ u ∈ U, M.ρ u = 1) (hUW : U ≤ W)
    (q : ℕ) [Fact q.Prime] (hq : (q : k) ≠ 0) (hW : ∀ w ∈ W, ∃ a : ℕ, w ^ (q ^ a) ∈ U)
    (t : G) (ht : t ∈ I) (htame : ∀ i ∈ I, ∃ a : ℕ, (t ^ a)⁻¹ * i ∈ W)
    (φ : G) (hgen : ∀ g, ∃ n : ℕ, (φ ^ n)⁻¹ * g ∈ I ⊔ U)
    (hχI : ∀ i ∈ I, χ i = 1) (hχU : ∀ u ∈ U, χ u = 1) (hχφ : (χ φ : k) = q)
    (m : ℕ) (hmq : (m : k) * q = 1)
    (hm : (QuotientGroup.mk φ : G ⧸ W)⁻¹ * QuotientGroup.mk t * QuotientGroup.mk φ
      = (QuotientGroup.mk t : G ⧸ W) ^ m)
    (hst : (QuotientGroup.mk φ : G ⧸ W) * QuotientGroup.mk t * (QuotientGroup.mk φ)⁻¹
      ∈ Subgroup.zpowers (QuotientGroup.mk t : G ⧸ W)) :
    finrank k (inflationImage M U)
      ≤ finrank k M.ρ.invariants + finrank k (M.dualTwist χ).ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_inflationImage_le_finrank_invariants_add_finrank_invariants_dualTwist.solution
