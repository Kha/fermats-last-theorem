import Mathlib
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_IsOpenImmersion_isRegularLocalRing_stalk_iff

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem solution
    {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] (u : U) :
    IsRegularLocalRing (X.presheaf.stalk (i.base u)) ↔ IsRegularLocalRing (U.presheaf.stalk u) := by
  let e : X.presheaf.stalk (i.base u) ≃+* U.presheaf.stalk u := (asIso (i.stalkMap u)).commRingCatIsoToRingEquiv
  exact ⟨fun h => IsRegularLocalRing.of_ringEquiv e, fun h => IsRegularLocalRing.of_ringEquiv e.symm⟩
