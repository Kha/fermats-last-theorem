import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_pi_cocyclesMk_zsmul

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.pi_cocyclesMk_zsmul
    {G : Type} [Group G] (A : Rep.{0} ℤ G) (n : ℕ) (m : ℤ) (x : (Fin n → G) → A)
    (hx : (inhomogeneousCochains.d A n).hom x = 0) (hmx : (inhomogeneousCochains.d A n).hom (m • x) = 0) :
    groupCohomology.π A n (groupCohomology.cocyclesMk (m • x) hmx) = m • groupCohomology.π A n (groupCohomology.cocyclesMk x hx) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_pi_cocyclesMk_zsmul.solution
