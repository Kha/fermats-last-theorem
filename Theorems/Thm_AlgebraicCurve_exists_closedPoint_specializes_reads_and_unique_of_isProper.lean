import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_ResidueDiscs
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_exists_closedPoint_specializes_reads_and_unique_of_isProper

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicCurve.exists_closedPoint_specializes_reads_and_unique_of_isProper
    {L : Type} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    (hrk : ∀ a b : ↥A, a ∈ maximalIdeal ↥A → b ≠ 0 → ∃ n : ℕ, b ∣ a ^ n)
    (hA : (A : Set L) ≠ Set.univ)
    [HenselianLocalRing ↥A]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F] [Algebra.EssFiniteType L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of ↥A))
    [IsIntegral X] [IsProper toBase] [Flat toBase] [LocallyOfFinitePresentation toBase]
    (hn : ∀ y : X, IsIntegrallyClosed (X.presheaf.stalk y))
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : ↥A, φ (algebraMap L F (a : L)) = SemistableModel.baseToFunctionField toBase a)
    (η : X) (hη : toBase.base η = closedPoint ↥A) (hηnc : ∃ y : X, η ⤳ y ∧ y ≠ η)

    (hdim : ∀ y : X, η ⤳ y → y ≠ η → ∀ y' : X, y ⤳ y' → y' = y)
    {Fbar : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
    (R : RegularProlongation A F Fbar)
    (hR : R.integers.toSubring = SemistableModel.localRing X φ η)
    (Q : Place (ResidueField ↥A) Fbar) :
    (∃ x : X, toBase.base x = closedPoint ↥A ∧ (∀ y : X, x ⤳ y → y = x) ∧ η ⤳ x ∧ η ≠ x ∧
      (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x → R.residue ⟨f, hf⟩ ∈ Q.toValuationSubring)) ∧
    (∀ (Q' : Place (ResidueField ↥A) Fbar) (x₁ x₂ : X),
        toBase.base x₁ = closedPoint ↥A → (∀ y : X, x₁ ⤳ y → y = x₁) →
        toBase.base x₂ = closedPoint ↥A → (∀ y : X, x₂ ⤳ y → y = x₂) → η ⤳ x₁ → η ⤳ x₂ →
        (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x₁ → R.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) →
        (∀ (f : F) (hf : f ∈ R.integers), f ∈ SemistableModel.localRing X φ x₂ → R.residue ⟨f, hf⟩ ∈ Q'.toValuationSubring) →
          x₁ = x₂) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_exists_closedPoint_specializes_reads_and_unique_of_isProper.solution
