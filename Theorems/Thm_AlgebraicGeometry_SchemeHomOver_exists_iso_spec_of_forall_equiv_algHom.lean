import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_SchemeHomOver_exists_iso_spec_of_forall_equiv_algHom

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra

theorem AlgebraicGeometry.SchemeHomOver.exists_iso_spec_of_forall_equiv_algHom
    {R : Type u} [CommRing R]
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R)) [IsAffine Y]
    (H : Type u) [CommRing H] [Algebra R H]
    (E : ∀ (T : Type u) [CommRing T] [Algebra R T],
      (H →ₐ[R] T) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R T))) y)
    (hE : ∀ (T T' : Type u) [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
      (a : T →ₐ[R] T') (φ : H →ₐ[R] T),
      (E T' (a.comp φ)).1 = Spec.map (CommRingCat.ofHom a.toRingHom) ≫ (E T φ).1) :
    ∃ i : Spec (CommRingCat.of H) ≅ Y,
      i.hom ≫ y = Spec.map (CommRingCat.ofHom (algebraMap R H)) ∧
      ∀ (T : Type u) [CommRing T] [Algebra R T] (φ : H →ₐ[R] T),
        (E T φ).1 = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ i.hom := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_SchemeHomOver_exists_iso_spec_of_forall_equiv_algHom.solution
