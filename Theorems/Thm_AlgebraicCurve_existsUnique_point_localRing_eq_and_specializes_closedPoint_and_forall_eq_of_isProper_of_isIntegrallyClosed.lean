import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase]

    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (P : Place L F) :
    ∃ pt : X,
      SemistableModel.localRing X φ pt = P.toValuationSubring.toSubring ∧
      (∀ pt' : X, SemistableModel.localRing X φ pt' = P.toValuationSubring.toSubring → pt' = pt) ∧
      (toBase.base pt).asIdeal = ⊥ ∧
      ∃ x : X, pt ⤳ x ∧ x ≠ pt ∧ toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧
        (∀ y : X, pt ⤳ y → y = pt ∨ y = x) ∧
        (∀ f : F, f ∈ SemistableModel.localRing X φ x →
          f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
            (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x, f * g = 1)) ∧

        (∀ x' : X, toBase.base x' = closedPoint ↥A → (∀ y : X, x' ⤳ y → y = x') →
          (∀ f : F, f ∈ SemistableModel.localRing X φ x' →
            f ∈ P.toValuationSubring ∧ ∃ h : P.evalAt f ∈ A,
              (IsUnit (⟨P.evalAt f, h⟩ : ↥A) ↔ ∃ g ∈ SemistableModel.localRing X φ x', f * g = 1)) → x' = x) ∧

        (∀ y : X, (toBase.base y).asIdeal = ⊥ → y ≠ genericPoint X →
          ∃ P' : Place L F, SemistableModel.localRing X φ y = P'.toValuationSubring.toSubring) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_existsUnique_point_localRing_eq_and_specializes_closedPoint_and_forall_eq_of_isProper_of_isIntegrallyClosed.solution
