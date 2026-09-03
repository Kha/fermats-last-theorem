import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_finrank_kaehlerDifferential_eq_of_smoothOfRelativeDimension

set_option autoImplicit false

open AlgebraicCurve CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.SemistableModel.finrank_kaehlerDifferential_eq_of_smoothOfRelativeDimension
    {A : Type} [CommRing A] [IsDomain A] {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
    {F : Type} [Field F] [Algebra L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A)) [IsIntegral X]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : A, φ (algebraMap L F (algebraMap A L a)) = SemistableModel.baseToFunctionField toBase a)
    (W : X.Opens) (hW : (W : Set X).Nonempty) (n : ℕ) [SmoothOfRelativeDimension n (W.ι ≫ toBase)] :
    Module.Finite F (KaehlerDifferential L F) ∧ Module.finrank F (KaehlerDifferential L F) = n := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_finrank_kaehlerDifferential_eq_of_smoothOfRelativeDimension.solution
