import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_zsmul_pi_cocyclesMk_eq_zero_of_eq_d

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.zsmul_pi_cocyclesMk_eq_zero_of_eq_d
    {G : Type} [Group G] (A : Rep.{0} ℤ G) (n : ℕ) (m : ℤ) (x : (Fin (n + 1) → G) → A)
    (hx : (inhomogeneousCochains.d A (n + 1)).hom x = 0) (y : (Fin n → G) → A)
    (h : m • x = (inhomogeneousCochains.d A n).hom y) :
    m • groupCohomology.π A (n + 1) (groupCohomology.cocyclesMk x hx) = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_zsmul_pi_cocyclesMk_eq_zero_of_eq_d.solution
