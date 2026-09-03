import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_inhomogeneousCochains_d_comp_eq_zero_of_d_eq_zero

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.inhomogeneousCochains_d_comp_eq_zero_of_d_eq_zero
    {k G : Type} [CommRing k] [Group G] {A B : Rep.{0} k G} (φ : A ⟶ B) (n : ℕ)
    (u : (Fin n → G) → A) (hu : ((inhomogeneousCochains A).d n (n + 1)).hom u = 0) :
    ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => φ.hom (u g)) = 0 := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_inhomogeneousCochains_d_comp_eq_zero_of_d_eq_zero.solution
