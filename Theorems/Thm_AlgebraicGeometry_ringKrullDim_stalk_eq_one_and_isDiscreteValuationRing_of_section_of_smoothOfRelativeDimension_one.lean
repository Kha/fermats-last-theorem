import Mathlib
import P2M.Util
import P2M.Sol.S_AlgebraicGeometry_ringKrullDim_stalk_eq_one_and_isDiscreteValuationRing_of_section_of_smoothOfRelativeDimension_one
attribute [-simp] RegularLocalRingQuotientAscent.dualNumberFst_apply

set_option autoImplicit false

open CategoryTheory open AlgebraicGeometry hiding exists_ker_stalkMap_eq_span_and_maximalIdeal_eq_of_section_of_smoothOfRelativeDimension_one open IsLocalRing

universe u

theorem AlgebraicGeometry.ringKrullDim_stalk_eq_one_and_isDiscreteValuationRing_of_section_of_smoothOfRelativeDimension_one
    {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 c]
    (σ : Spec (CommRingCat.of k) ⟶ X) (hσ : σ ≫ c = 𝟙 _) :
    ringKrullDim (X.presheaf.stalk (σ.base (closedPoint k))) = 1 ∧
      ∃ _ : IsDomain (X.presheaf.stalk (σ.base (closedPoint k))), IsDiscreteValuationRing (X.presheaf.stalk (σ.base (closedPoint k))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ringKrullDim_stalk_eq_one_and_isDiscreteValuationRing_of_section_of_smoothOfRelativeDimension_one.solution
