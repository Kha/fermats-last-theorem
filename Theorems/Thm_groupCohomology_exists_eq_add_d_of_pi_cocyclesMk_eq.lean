import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_exists_eq_add_d_of_pi_cocyclesMk_eq

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.exists_eq_add_d_of_pi_cocyclesMk_eq
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (n : ℕ) (x x' : (Fin (n + 1) → G) → A)
    (hx : (inhomogeneousCochains.d A (n + 1)).hom x = 0) (hx' : (inhomogeneousCochains.d A (n + 1)).hom x' = 0)
    (h : groupCohomology.π A (n + 1) (groupCohomology.cocyclesMk x hx) = groupCohomology.π A (n + 1) (groupCohomology.cocyclesMk x' hx')) :
    ∃ y : (Fin n → G) → A, x = x' + (inhomogeneousCochains.d A n).hom y := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_exists_eq_add_d_of_pi_cocyclesMk_eq.solution
