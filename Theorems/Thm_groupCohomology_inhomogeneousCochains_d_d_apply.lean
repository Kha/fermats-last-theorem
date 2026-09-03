import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_inhomogeneousCochains_d_d_apply

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.inhomogeneousCochains_d_d_apply
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (n : ℕ) (y : (Fin n → G) → A) :
    (inhomogeneousCochains.d A (n + 1)).hom ((inhomogeneousCochains.d A n).hom y) = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_inhomogeneousCochains_d_d_apply.solution
