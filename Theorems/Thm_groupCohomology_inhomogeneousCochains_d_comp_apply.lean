import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_inhomogeneousCochains_d_comp_apply

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.inhomogeneousCochains_d_comp_apply
    {k G : Type} [CommRing k] [Group G] {A B : Rep.{0} k G} (φ : A ⟶ B) (n : ℕ)
    (x : (Fin n → G) → A) :
    ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => φ.hom (x g)) =
      fun g => φ.hom (((inhomogeneousCochains A).d n (n + 1)).hom x g) := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_inhomogeneousCochains_d_comp_apply.solution
