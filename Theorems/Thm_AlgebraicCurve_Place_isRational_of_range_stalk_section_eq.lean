import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

theorem AlgebraicCurve.Place.isRational_of_range_stalk_section_eq
    {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (CommRingCat.of k)) [IsIntegral X]
    (σ : Spec (CommRingCat.of k) ⟶ X) (hσ : σ ≫ c = 𝟙 _) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∀ (v : AlgebraicCurve.Place k X.functionField),
      (algebraMap (X.presheaf.stalk (σ.base (IsLocalRing.closedPoint k))) X.functionField).range =
        v.toValuationSubring.toSubring → v.IsRational := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_Place_isRational_of_range_stalk_section_eq.solution
