import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_cocycles1_forall_apply_mul_right_eq_iff_apply_eq_zero

open CategoryTheory Module groupCohomology

universe u
theorem groupCohomology.cocycles1_forall_apply_mul_right_eq_iff_apply_eq_zero {k G : Type u} [CommRing k] [Group G] {M : Rep k G} (c : cocycles₁ M) (u : G) :
    (∀ g : G, c (g * u) = c g) ↔ c u = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_cocycles1_forall_apply_mul_right_eq_iff_apply_eq_zero.solution
