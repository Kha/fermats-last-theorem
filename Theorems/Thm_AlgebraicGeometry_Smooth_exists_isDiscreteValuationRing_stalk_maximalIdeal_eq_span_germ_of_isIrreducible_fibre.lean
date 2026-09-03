import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_Smooth_exists_isDiscreteValuationRing_stalk_maximalIdeal_eq_span_germ_of_isIrreducible_fibre
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.Smooth.exists_isDiscreteValuationRing_stalk_maximalIdeal_eq_span_germ_of_isIrreducible_fibre
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f]
    (hirr : IsIrreducible (f.base ⁻¹' {IsLocalRing.closedPoint R})) :
    ∃ ξ : X, f.base ξ = IsLocalRing.closedPoint R ∧
      (∀ Z ∈ irreducibleComponents {x : X // f.base x = IsLocalRing.closedPoint R}, ∃ z ∈ Z, z.1 = ξ) ∧
      ∃ _ : IsDomain (X.presheaf.stalk ξ), IsDiscreteValuationRing (X.presheaf.stalk ξ) ∧
        IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) =
          Ideal.span {X.presheaf.Γgerm ξ (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ϖ))} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Smooth_exists_isDiscreteValuationRing_stalk_maximalIdeal_eq_span_germ_of_isIrreducible_fibre.solution
