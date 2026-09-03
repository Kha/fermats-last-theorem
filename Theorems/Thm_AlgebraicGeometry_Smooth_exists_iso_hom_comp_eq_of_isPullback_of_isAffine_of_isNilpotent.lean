import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover

universe u
theorem AlgebraicGeometry.Smooth.exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent
    {T' T : Type u} [CommRing T'] [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π)
    (hker : IsNilpotent (RingHom.ker π))
    {V Y Y' : Scheme.{u}} (v : V ⟶ Spec (CommRingCat.of T))
    (q : Y ⟶ Spec (CommRingCat.of T')) [IsAffine Y] (hq : Smooth q)
    (q' : Y' ⟶ Spec (CommRingCat.of T')) [IsAffine Y'] (hq' : Smooth q')
    (g : V ⟶ Y) (hg : IsPullback g v q (Spec.map (CommRingCat.ofHom π)))
    (g' : V ⟶ Y') (hg' : IsPullback g' v q' (Spec.map (CommRingCat.ofHom π))) :
    ∃ φ : Y ≅ Y', φ.hom ≫ q' = q ∧ g ≫ φ.hom = g' := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_iso_hom_comp_eq_of_isPullback_of_isAffine_of_isNilpotent.solution
