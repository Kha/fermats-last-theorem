import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_isFinite_of_unit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_isFinite
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_FiniteBySections_of_finiteBySections_unit

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f]
    (h𝒪 : Scheme.Modules.FiniteBySections (SheafOfModules.unit X.ringCatSheaf : X.Modules) f)
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Scheme.Modules.FiniteBySections M f := by
  haveI : IsFinite f := AlgebraicGeometry.Scheme.Modules.FiniteBySections.isFinite_of_unit f h𝒪
  exact AlgebraicGeometry.Scheme.Modules.FiniteBySections.of_isFinite f M hM
