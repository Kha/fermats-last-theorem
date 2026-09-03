import Mathlib
import P2M.Util
namespace P2MW.S_groupCohomology_pi_cocyclesMk_zsmul

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {G : Type} [Group G] (A : Rep.{0} ℤ G) (n : ℕ) (m : ℤ) (x : (Fin n → G) → A)
    (hx : (inhomogeneousCochains.d A n).hom x = 0) (hmx : (inhomogeneousCochains.d A n).hom (m • x) = 0) :
    groupCohomology.π A n (groupCohomology.cocyclesMk (m • x) hmx) = m • groupCohomology.π A n (groupCohomology.cocyclesMk x hx) := by
  have h : groupCohomology.cocyclesMk (m • x) hmx = m • groupCohomology.cocyclesMk x hx := by
    apply (ModuleCat.mono_iff_injective (iCocycles A n)).1 inferInstance
    rw [map_zsmul, iCocycles_mk, iCocycles_mk]
  rw [h, map_zsmul]
