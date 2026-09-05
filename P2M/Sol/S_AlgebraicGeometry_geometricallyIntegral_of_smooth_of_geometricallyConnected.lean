import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_IsRegularLocalRing_isDomain
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GeomIntKit

theorem isIntegral_of_smooth_of_connectedSpace {K : Type u} [Field K] {X : Scheme.{u}}
    (t : X ⟶ Spec (CommRingCat.of K)) [Smooth t] [ConnectedSpace X] : IsIntegral X := by
  haveI : LocallyOfFiniteType t := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian t
  exact AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
    X fun x => by
      haveI := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := t) x
      exact IsRegularLocalRing.isDomain _

end GeomIntKit

open GeomIntKit in
theorem solution
    {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f] :
    GeometricallyIntegral f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  haveI : Smooth (pullback.snd f y) := MorphismProperty.pullback_snd (P := @Smooth) _ _ ‹_›
  haveI : ConnectedSpace ↥(pullback f y) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd f y)
  haveI : IsIntegral (pullback f y) := isIntegral_of_smooth_of_connectedSpace (pullback.snd f y)
  exact IsIntegral.of_isIso h.isoPullback.inv

