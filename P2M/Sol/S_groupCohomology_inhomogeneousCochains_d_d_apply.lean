import Mathlib
import P2M.Util
namespace P2MW.S_groupCohomology_inhomogeneousCochains_d_d_apply

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (n : ℕ) (y : (Fin n → G) → A) :
    (inhomogeneousCochains.d A (n + 1)).hom ((inhomogeneousCochains.d A n).hom y) = 0 := by
  have h := congrArg (fun T => (ModuleCat.Hom.hom T) y) (inhomogeneousCochains.d_comp_d (A := A) (n := n))
  simpa using h
