import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_pi_cocyclesMk_eq_zero_of_eq_zero

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.pi_cocyclesMk_eq_zero_of_eq_zero
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (n : ℕ) (x : (Fin n → G) → A)
    (hx : (inhomogeneousCochains.d A n).hom x = 0) (h0 : x = 0) :
    groupCohomology.π A n (groupCohomology.cocyclesMk x hx) = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_pi_cocyclesMk_eq_zero_of_eq_zero.solution
