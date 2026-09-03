import Mathlib
import P2M.Util
namespace P2MW.S_groupCohomology_inhomogeneousCochains_d_comp_eq_zero_of_d_eq_zero

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {k G : Type} [CommRing k] [Group G] {A B : Rep.{0} k G} (φ : A ⟶ B) (n : ℕ)
    (u : (Fin n → G) → A) (hu : ((inhomogeneousCochains A).d n (n + 1)).hom u = 0) :
    ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => φ.hom (u g)) = 0 := by
  let ι := groupCohomology.cochainsMap (MonoidHom.id G) φ
  have hι : ∀ (m : ℕ) (x : (Fin m → G) → A), (ι.f m).hom x = fun g => φ.hom (x g) := fun m x => rfl
  have hcomm : ((inhomogeneousCochains B).d n (n + 1)).hom ((ι.f n).hom u) =
      (ι.f (n + 1)).hom (((inhomogeneousCochains A).d n (n + 1)).hom u) :=
    LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (ι.comm n (n + 1))) u
  rw [← hι, hcomm, hu, map_zero]
