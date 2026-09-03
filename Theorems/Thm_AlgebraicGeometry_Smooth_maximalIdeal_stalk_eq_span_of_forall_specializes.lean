import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_maximalIdeal_stalk_eq_span_of_forall_specializes

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Topology

theorem AlgebraicGeometry.Smooth.maximalIdeal_stalk_eq_span_of_forall_specializes
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgen : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    IsLocalRing.maximalIdeal (T.presheaf.stalk η) =
      Ideal.span {(T.presheaf.germ ⊤ η trivial).hom ((t.appTop).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ))} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_maximalIdeal_stalk_eq_span_of_forall_specializes.solution
