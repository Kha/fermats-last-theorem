import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_flat_of_iso_generic

set_option autoImplicit false

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.exists_iso_hom_comp_eq_of_isClosedImmersion_of_flat_of_iso_generic
    {R : Type} [CommRing R] [IsDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R))
    (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂] [Algebra R A₁] [Algebra R A₂]
    [Module.Flat R A₁] [Module.Flat R A₂]
    (i₁ : Spec (CommRingCat.of A₁) ⟶ Y) (i₂ : Spec (CommRingCat.of A₂) ⟶ Y)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h₁ : i₁ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A₁)))
    (h₂ : i₂ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A₂)))
    (eK : Spec (CommRingCat.of (K ⊗[R] A₁)) ≅ Spec (CommRingCat.of (K ⊗[R] A₂)))
    (heK : eK.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₂ →+* K ⊗[R] A₂)) ≫ i₂ =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom : A₁ →+* K ⊗[R] A₁)) ≫ i₁) :
    ∃ e : Spec (CommRingCat.of A₁) ≅ Spec (CommRingCat.of A₂), e.hom ≫ i₂ = i₁ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_iso_hom_comp_eq_of_isClosedImmersion_of_flat_of_iso_generic.solution
