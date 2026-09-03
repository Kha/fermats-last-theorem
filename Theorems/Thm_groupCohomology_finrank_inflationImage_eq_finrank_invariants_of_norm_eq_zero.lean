import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_inflationImage_eq_finrank_invariants_of_norm_eq_zero

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finrank_inflationImage_eq_finrank_invariants_of_norm_eq_zero
    {k G : Type u} [Field k] [Group G] (M : Rep k G) [FiniteDimensional k M]
    (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)]
    {φ : G} (hφ : ∀ x : G ⧸ N, x ∈ Subgroup.zpowers (QuotientGroup.mk φ : G ⧸ N))
    (hN : (M.quotientToInvariants N).ρ.norm = 0) :
    Module.finrank k (groupCohomology.inflationImage M N) = Module.finrank k M.ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_inflationImage_eq_finrank_invariants_of_norm_eq_zero.solution
