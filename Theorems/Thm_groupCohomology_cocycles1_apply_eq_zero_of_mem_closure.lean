import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_cocycles1_apply_eq_zero_of_mem_closure

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.cocycles1_apply_eq_zero_of_mem_closure {k G : Type u} [CommRing k] [Group G] {M : Rep k G} (c : cocycles₁ M) {s : Set G}
    (hs : ∀ g ∈ s, c g = 0) {g : G} (hg : g ∈ Subgroup.closure s) : c g = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_cocycles1_apply_eq_zero_of_mem_closure.solution
