import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_cocycles1_unramified_iff_mem_inflationImage_sup

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.exists_cocycles1_unramified_iff_mem_inflationImage_sup {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (I U : Subgroup G) [I.Normal] [U.Normal]
    (hU : ∀ u ∈ U, M.ρ u = 1) (x : H1 M) :
    (∃ c : cocycles₁ M, H1π M c = x ∧ (∀ u ∈ U, c u = 0) ∧
        ∃ m : M, ∀ g ∈ I, c g = M.ρ g m - m)
      ↔ x ∈ inflationImage M (I ⊔ U) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_cocycles1_unramified_iff_mem_inflationImage_sup.solution
