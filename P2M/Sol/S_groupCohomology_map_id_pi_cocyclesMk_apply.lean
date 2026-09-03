import Mathlib
import Theorems.Thm_groupCohomology_map_pi_cocyclesMk_apply
import P2M.Util
namespace P2MW.S_groupCohomology_map_id_pi_cocyclesMk_apply

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {k G : Type} [CommRing k] [Group G] {A B : Rep.{0} k G}
    (φ : A ⟶ B) (n : ℕ) (x : (Fin n → G) → A)
    (hx : (inhomogeneousCochains.d A n).hom x = 0)
    (hx' : (inhomogeneousCochains.d B n).hom (fun g => φ.hom (x g)) = 0) :
    (groupCohomology.map (MonoidHom.id G) φ n).hom (groupCohomology.π A n (groupCohomology.cocyclesMk x hx)) =
      groupCohomology.π B n (groupCohomology.cocyclesMk (fun g => φ.hom (x g)) hx') := by
  exact groupCohomology.map_pi_cocyclesMk_apply (MonoidHom.id G) φ n x hx hx'
