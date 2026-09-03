import Mathlib
import Definitions.Def_AlgebraicGeometry_PolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_eq_of_isPullback
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_geomFibreH0Finrank_pullback_inv_of_iso

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {S : Type u} [CommRing S] {A A' : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of S)) (f' : A' ⟶ Spec (CommRingCat.of S))
    (e : A ≅ A') (he : e.hom ≫ f' = f) (M : A.Modules)
    (k : Type u) [Field k] (sk : S →+* k) :
    Scheme.Modules.geomFibreH0Finrank f' ((Scheme.Modules.pullback e.inv).obj M) k sk =
      Scheme.Modules.geomFibreH0Finrank f M k sk := by
  have hsq : IsPullback e.inv f' f (Spec.map (CommRingCat.ofHom (RingHom.id S))) := by
    have hid : Spec.map (CommRingCat.ofHom (RingHom.id S)) = 𝟙 _ := by
      rw [CommRingCat.ofHom_id]; exact Spec.map_id _
    rw [hid]
    exact IsPullback.of_horiz_isIso ⟨by rw [← he, e.inv_hom_id_assoc, Category.comp_id]⟩
  have h := AlgebraicGeometry.Scheme.Modules.geomFibreH0Finrank_eq_of_isPullback (RingHom.id S) f f' e.inv hsq M
    ((Scheme.Modules.pullback e.inv).obj M) (Iso.refl _) k sk
  rw [RingHom.comp_id] at h
  exact h
