import Mathlib
import P2M.Util
import P2M.Sol.S_groupCohomology_map_pi_cocyclesMk_apply

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.map_pi_cocyclesMk_apply
    {k G H : Type} [CommRing k] [Group G] [Group H] {A : Rep.{0} k H} {B : Rep.{0} k G}
    (f : G →* H) (φ : Rep.res f A ⟶ B) (n : ℕ) (x : (Fin n → H) → A)
    (hx : (inhomogeneousCochains.d A n).hom x = 0)
    (hx' : (inhomogeneousCochains.d B n).hom (fun g => φ.hom (x (f ∘ g))) = 0) :
    (groupCohomology.map f φ n).hom (groupCohomology.π A n (groupCohomology.cocyclesMk x hx)) =
      groupCohomology.π B n (groupCohomology.cocyclesMk (fun g => φ.hom (x (f ∘ g))) hx') := by p2m_exact_reverting @_root_.P2MW.S_groupCohomology_map_pi_cocyclesMk_apply.solution
