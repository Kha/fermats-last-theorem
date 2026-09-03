import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_moduleFinite_globalSections_of_isProper_of_isAffineHom
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [IsProper f] [IsAffineHom f] :
    letI : Algebra R Γ(X, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    Module.Finite R Γ(X, ⊤) := by
  haveI : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  haveI : IsAffine X := isAffine_of_isAffineHom f
  have hfin : f.appTop.hom.Finite := Scheme.Hom.finite_appTop f
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.surjective
  have hcomp : ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.Finite := by
    rw [CommRingCat.hom_comp]
    exact hfin.comp (RingHom.Finite.of_surjective _ hsurj)
  exact hcomp
