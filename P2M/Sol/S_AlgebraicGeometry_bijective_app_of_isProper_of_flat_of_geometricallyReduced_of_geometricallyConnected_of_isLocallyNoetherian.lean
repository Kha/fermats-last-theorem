import Mathlib
import Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField_of_isLocallyNoetherian
import Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected_of_isLocallyNoetherian
attribute [-instance] AdicCompletion.instIsLocalRingMaximalIdeal

open AlgebraicGeometry CategoryTheory

universe u

open CategoryTheory.Limits

theorem solution
    {X B : Scheme.{u}} [IsLocallyNoetherian B] (p : X ⟶ B) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [GeometricallyReduced p] [GeometricallyConnected p] (U : B.Opens) :
    Function.Bijective (p.app U) := by
  refine AlgebraicGeometry.bijective_app_of_isProper_of_flat_of_forall_bijective_appTop_fiberToSpecResidueField_of_isLocallyNoetherian
    p (fun b => ?_) U
  haveI : UniversallyClosed (pullback.snd p (B.fromSpecResidueField b)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : GeometricallyReduced (pullback.snd p (B.fromSpecResidueField b)) := inferInstance
  haveI : GeometricallyConnected (pullback.snd p (B.fromSpecResidueField b)) := inferInstance
  exact AlgebraicGeometry.bijective_appTop_of_universallyClosed_of_geometricallyReduced_of_geometricallyConnected
    (K := B.residueField b) (pullback.snd p (B.fromSpecResidueField b))
