import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one

set_option autoImplicit false

p2m_open "CategoryTheory AlgebraicGeometry~exists_algHom_retraction_stalk_and_ker_le_span_sup_sq_of_section_of_smoothOfRelativeDimension_one IsLocalRing"

universe u

theorem AlgebraicGeometry.exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one
    {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of A))
    [SmoothOfRelativeDimension 1 c]
    (σ : Spec (CommRingCat.of A) ⟶ X) (hσ : σ ≫ c = 𝟙 _) :
    ∃ t : X.presheaf.stalk (σ.base (closedPoint A)),
      RingHom.ker (Scheme.Hom.stalkMap σ (closedPoint A)).hom = Ideal.span {t} ∧
      maximalIdeal (X.presheaf.stalk (σ.base (closedPoint A))) =
        Ideal.span {t} ⊔ (maximalIdeal A).map ((X.presheaf.germ ⊤ (σ.base (closedPoint A)) trivial).hom.comp
          (c.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one.solution
