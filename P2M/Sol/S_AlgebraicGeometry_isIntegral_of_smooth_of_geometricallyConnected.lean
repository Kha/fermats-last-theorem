import Mathlib
import Theorems.Thm_AlgebraicGeometry_isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk
import Theorems.Thm_AlgebraicGeometry_Smooth_isRegularLocalRing_stalk
import Theorems.Thm_IsRegularLocalRing_isDomain
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isIntegral_of_smooth_of_geometricallyConnected
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    (hsm : Smooth t) (hgc : GeometricallyConnected t)
    (e : Spec (CommRingCat.of k) ⟶ X) (he : e ≫ t = 𝟙 _) :
    IsIntegral X := by
  haveI := hsm
  haveI := hgc
  haveI : LocallyOfFiniteType t := inferInstance
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian t
  haveI : ConnectedSpace X := by
    exact GeometricallyConnected.connectedSpace_of_subsingleton t
  exact AlgebraicGeometry.isIntegral_of_isLocallyNoetherian_of_connectedSpace_of_forall_isDomain_stalk X
    fun x => by
      haveI := AlgebraicGeometry.Smooth.isRegularLocalRing_stalk (f := t) x
      exact IsRegularLocalRing.isDomain _
