import Mathlib
import P2M.Util
namespace P2MW.S_groupCohomology_inhomogeneousCochains_d_comp_apply

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem solution
    {k G : Type} [CommRing k] [Group G] {A B : Rep.{0} k G} (φ : A ⟶ B) (n : ℕ)
    (x : (Fin n → G) → A) :
    ((inhomogeneousCochains B).d n (n + 1)).hom (fun g => φ.hom (x g)) =
      fun g => φ.hom (((inhomogeneousCochains A).d n (n + 1)).hom x g) := by
  have h := (cochainsMap (MonoidHom.id G) φ).comm n (n + 1)

  have h2 := congrArg (fun T => (ModuleCat.Hom.hom T) x) h
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, cochainsMap_id_f_hom_eq_compLeft] at h2
  exact h2
