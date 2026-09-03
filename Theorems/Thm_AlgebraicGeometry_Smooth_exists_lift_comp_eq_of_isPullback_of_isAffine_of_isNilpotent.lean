import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
theorem AlgebraicGeometry.Smooth.exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {Z V : Scheme.{u}} (qZ : Z ⟶ Spec (CommRingCat.of T')) [IsAffine Z]
    (gZ : V ⟶ Z) (fV : V ⟶ Spec (CommRingCat.of T)) (hgZ : IsPullback gZ fV qZ (Spec.map (CommRingCat.ofHom π)))
    {Y U : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of T')) [IsAffine Y] [Smooth q]
    (g : U ⟶ Y) (fU : U ⟶ Spec (CommRingCat.of T)) (hg : IsPullback g fU q (Spec.map (CommRingCat.ofHom π)))
    (h : V ⟶ U) (hh : h ≫ fU = fV) :
    ∃ hZ : Z ⟶ Y, hZ ≫ q = qZ ∧ gZ ≫ hZ = h ≫ g := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_lift_comp_eq_of_isPullback_of_isAffine_of_isNilpotent.solution
