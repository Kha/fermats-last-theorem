import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory open AlgebraicGeometry hiding isIntegral_of_smooth_of_preconnectedSpace

universe u

theorem AlgebraicGeometry.Smooth.algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (p : Y) (hp : f.base p = IsLocalRing.closedPoint R)
    [Algebra R (Y.presheaf.stalk p)]
    (halg : Y.fromSpecStalk p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk p)))) :
    algebraMap R (Y.presheaf.stalk p) ϖ ≠ 0 ∧
      (Ideal.span {algebraMap R (Y.presheaf.stalk p) ϖ}).IsPrime := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_algebraMap_stalk_ne_zero_and_isPrime_span_of_apply_eq_closedPoint.solution
