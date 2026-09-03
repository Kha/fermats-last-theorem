import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_ker_ideal_eq_span_of_span_germ_eq_maximalIdeal_of_forall_isUnit_germ

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

theorem AlgebraicGeometry.Scheme.Hom.ker_ideal_eq_span_of_span_germ_eq_maximalIdeal_of_forall_isUnit_germ
    {X : Scheme.{u}} [IsIntegral X] {K : Type u} [Field K]
    (j : Spec (CommRingCat.of K) ⟶ X) [IsClosedImmersion j]
    (W : X.Opens) (hPW : j.base (IsLocalRing.closedPoint K) ∈ W) (a : Γ(X, W))

    (ha0 : j.app W a = 0)

    (hagen : Ideal.span {X.presheaf.germ W (j.base (IsLocalRing.closedPoint K)) hPW a} =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (j.base (IsLocalRing.closedPoint K))))

    (haU : ∀ (z : X) (hz : z ∈ W), z ≠ j.base (IsLocalRing.closedPoint K) → IsUnit (X.presheaf.germ W z hz a))

    (hW : ∃ z ∈ W, z ≠ j.base (IsLocalRing.closedPoint K)) :
    ∀ (U : X.affineOpens) (hU : (U : X.Opens) ≤ W),
      j.ker.ideal U = Ideal.span {X.presheaf.map (homOfLE hU).op a} ∧
        X.presheaf.map (homOfLE hU).op a ∈ nonZeroDivisors Γ(X, U) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_ker_ideal_eq_span_of_span_germ_eq_maximalIdeal_of_forall_isUnit_germ.solution
