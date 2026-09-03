import Mathlib
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_isIntegral_pullback_and_isIntegral_pullback_fst_comp_of_smooth_of_geometricallyConnected_pullback_snd_specMap
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

universe u

theorem AlgebraicGeometry.isIntegral_pullback_and_isIntegral_pullback_fst_comp_of_smooth_of_geometricallyConnected_pullback_snd_specMap
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (L : Type u) [Field L] [Algebra A L] [IsFractionRing A L]
    {X T : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A)) [IsIntegral X] [LocallyOfFiniteType c]
    (hne : Nonempty ↑(pullback c (specMap A L)))
    (t : T ⟶ Spec (CommRingCat.of A)) [Smooth t]
    [GeometricallyConnected (pullback.snd t (specMap A L))] :
    IsIntegral ↑(pullback c t) ∧ IsIntegral ↑(pullback c (pullback.fst t t ≫ t)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isIntegral_pullback_and_isIntegral_pullback_fst_comp_of_smooth_of_geometricallyConnected_pullback_snd_specMap.solution
