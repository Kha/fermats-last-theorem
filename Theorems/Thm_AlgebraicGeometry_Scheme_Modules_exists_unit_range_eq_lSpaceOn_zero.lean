import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlacesOf
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero
attribute [-instance] AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Modules.exists_unit_range_eq_lSpaceOn_zero
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [SmoothOfRelativeDimension 1 x] :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    ∃ φ : ∀ U : X.Opens, Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U) →+ (X.functionField : Type u),
      (∀ (U : X.Opens) [Nonempty U] (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U m = (X.germToFunctionField U).hom (show Γ(X, U) from m)) ∧
      (∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
          ∀ m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U),
            φ V ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf : X.Modules)).map (homOfLE h).op m)
              = φ U m) ∧
      (∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), U)),
          φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m) ∧
      (∀ U : X.Opens, Nonempty U → Function.Injective (φ U)) ∧
      (∀ U : X.Opens, IsAffineOpen U → Nonempty U →
          Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U)
            (0 : AlgebraicCurve.Divisor K X.functionField) : Set X.functionField)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_unit_range_eq_lSpaceOn_zero.solution
