import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology

theorem AlgebraicGeometry.maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ c = 𝟙 _)
    (t : X.presheaf.stalk (σ.base (IsLocalRing.closedPoint A)))
    (ht : RingHom.ker (σ.stalkMap (IsLocalRing.closedPoint A)).hom = Ideal.span {t}) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk (σ.base (genericPoint ↥(Spec (CommRingCat.of A))))) =
      Ideal.span {(X.presheaf.stalkSpecializes
        (((genericPoint_specializes (IsLocalRing.closedPoint A)).map σ.continuous) :
          σ.base (genericPoint ↥(Spec (CommRingCat.of A))) ⤳ σ.base (IsLocalRing.closedPoint A))).hom t} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_maximalIdeal_stalk_eq_span_stalkSpecializes_of_ker_stalkMap_eq_span.solution
