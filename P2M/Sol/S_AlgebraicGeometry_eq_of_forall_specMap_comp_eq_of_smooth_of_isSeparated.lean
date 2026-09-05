import Mathlib
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_isReduced_of_flat_of_isReduced_pullback_of_isFractionRing
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_smooth_of_isSeparated

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {R : Type u} [CommRing R] [IsDomain R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower R K Ω]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    [Smooth f] [IsSeparated g]
    (φ ψ : X ⟶ Y) (hφ : φ ≫ g = f) (hψ : ψ ≫ g = f)
    (h : ∀ x : Spec (CommRingCat.of Ω) ⟶ X,
      x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Ω)) → x ≫ φ = x ≫ ψ) :
    φ = ψ := by

  haveI : Flat f := inferInstance
  haveI : LocallyOfFinitePresentation f := inferInstance

  haveI : IsReduced (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
    AlgebraicGeometry.isReduced_of_smooth_over_field (g := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) inferInstance
  haveI : IsReduced X := AlgebraicGeometry.isReduced_of_flat_of_isReduced_pullback_of_isFractionRing K f
  exact AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated K Ω f g φ ψ hφ hψ h

