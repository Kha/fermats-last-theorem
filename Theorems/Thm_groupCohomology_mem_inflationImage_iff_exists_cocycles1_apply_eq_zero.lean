import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses
import P2M.Util
import P2M.Sol.S_groupCohomology_mem_inflationImage_iff_exists_cocycles1_apply_eq_zero

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.mem_inflationImage_iff_exists_cocycles1_apply_eq_zero {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (N : Subgroup G) [N.Normal] (x : H1 M) :
    x ∈ inflationImage M N ↔ ∃ c : cocycles₁ M, H1π M c = x ∧ ∀ n ∈ N, c n = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_mem_inflationImage_iff_exists_cocycles1_apply_eq_zero.solution
