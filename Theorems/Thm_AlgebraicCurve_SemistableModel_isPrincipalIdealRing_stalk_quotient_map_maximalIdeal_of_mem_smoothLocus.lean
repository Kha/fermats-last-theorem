import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_isPrincipalIdealRing_stalk_quotient_map_maximalIdeal_of_mem_smoothLocus

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.SemistableModel.isPrincipalIdealRing_stalk_quotient_map_maximalIdeal_of_mem_smoothLocus
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint ↥A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus) :
    let c : ↥A →+* X.presheaf.stalk x :=
      (X.presheaf.germ ⊤ x trivial).hom.comp (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv.hom)
    let I : Ideal (X.presheaf.stalk x) := (maximalIdeal ↥A).map c
    IsDomain (X.presheaf.stalk x ⧸ I) ∧ IsPrincipalIdealRing (X.presheaf.stalk x ⧸ I) ∧
      ¬ IsField (X.presheaf.stalk x ⧸ I) ∧
      ∀ b : X.presheaf.stalk x, ∃ a : ↥A, b - c a ∈ maximalIdeal (X.presheaf.stalk x) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_isPrincipalIdealRing_stalk_quotient_map_maximalIdeal_of_mem_smoothLocus.solution
