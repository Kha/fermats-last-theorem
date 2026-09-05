import Mathlib
import Theorems.Thm_AlgebraicGeometry_GeometricallyReduced_of_isReduced_of_perfectField
import P2M.Util
namespace P2MW.S_AlgebraicGeometry_isReduced_pullback_of_isReduced_pullback_of_perfectField

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem solution
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {κ₀ : Type u} [Field κ₀] [PerfectField κ₀] (x₀ : Spec (CommRingCat.of κ₀) ⟶ S)
    [IsReduced (pullback f x₀)]
    {k : Type u} [Field k] (ι : κ₀ →+* k) (x : Spec (CommRingCat.of k) ⟶ S)
    (hx : x = Spec.map (CommRingCat.ofHom ι) ≫ x₀) :
    IsReduced (pullback f x) := by
  subst hx
  haveI : GeometricallyReduced (pullback.snd f x₀) :=
    AlgebraicGeometry.GeometricallyReduced.of_isReduced_of_perfectField (pullback.snd f x₀)
  haveI : IsReduced (pullback (pullback.snd f x₀) (Spec.map (CommRingCat.ofHom ι))) :=
    pullback_of_geometrically (GeometricallyReduced.geometrically_isReduced (f := pullback.snd f x₀)) k
      (Spec.map (CommRingCat.ofHom ι))
  exact isReduced_of_isOpenImmersion (pullbackLeftPullbackSndIso f x₀ (Spec.map (CommRingCat.ofHom ι))).inv

