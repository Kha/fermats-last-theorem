import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
import P2M.Sol.S_groupCohomology_finrank_inflationImage_eq_finrank_invariants

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.finrank_inflationImage_eq_finrank_invariants {k G : Type u} [Field k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Finite G] [Fintype (G ⧸ S)] [FiniteDimensional k A]
    {φ : G} (hφ : ∀ x : G ⧸ S, x ∈ Subgroup.zpowers (QuotientGroup.mk φ : G ⧸ S))
    (hN : (A.quotientToInvariants S).ρ.norm = 0) :
    finrank k (inflationImage A S) = finrank k A.ρ.invariants := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_finrank_inflationImage_eq_finrank_invariants.solution
