import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_residueChar_localRing_of_mem_smoothLocus_of_isDiscreteValuationRing

set_option autoImplicit false

open AlgebraicCurve IsLocalRing CategoryTheory AlgebraicGeometry

theorem AlgebraicCurve.SemistableModel.exists_etaleCoordinate_residueChar_localRing_of_mem_smoothLocus_of_isDiscreteValuationRing
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    [IsAlgClosed (ResidueField A)]
    {L : Type} [Field L] [Algebra A L] [IsFractionRing A L]
    {F : Type} [Field F] [Algebra L F] [IsCurveOver L F]
    (X : Scheme.{0}) (toBase : X ⟶ Spec (CommRingCat.of A))
    [IsIntegral X] [LocallyOfFinitePresentation toBase]
    (φ : F ≃+* X.functionField)
    (hφ : ∀ a : A, φ (algebraMap L F (algebraMap A L a)) = SemistableModel.baseToFunctionField toBase a)
    (x : X) (hx : toBase.base x = closedPoint A) (hxc : ∀ y : X, x ⤳ y → y = x) (hxs : x ∈ toBase.smoothLocus) :
    ∃ (φT : Polynomial A →+* ↥(SemistableModel.localRing X φ x))
      (χ : ↥(SemistableModel.localRing X φ x) →+* ResidueField A),
      (∀ a : A, algebraMap L F (algebraMap A L a) ∈ SemistableModel.localRing X φ x) ∧
      (∀ a : A, ((φT (Polynomial.C a) : ↥(SemistableModel.localRing X φ x)) : F) = algebraMap L F (algebraMap A L a)) ∧
      (∀ a : A, χ (φT (Polynomial.C a)) = IsLocalRing.residue A a) ∧
      χ (φT Polynomial.X) = 0 ∧
      (∃ _ : IsLocalRing ↥(SemistableModel.localRing X φ x),
        RingHom.ker χ = IsLocalRing.maximalIdeal ↥(SemistableModel.localRing X φ x) ∧
        IsLocalRing.maximalIdeal ↥(SemistableModel.localRing X φ x) = Ideal.span {φT (Polynomial.C ϖ), φT Polynomial.X}) ∧
      Function.Surjective χ ∧
      φT.FormallySmooth ∧ φT.FormallyUnramified ∧ φT.EssFiniteType ∧
      φT Polynomial.X ∉ Ideal.span {φT (Polynomial.C ϖ)} ∧
      (∀ f : F, ∃ g h : ↥(SemistableModel.localRing X φ x), (h : F) ≠ 0 ∧ f * (h : F) = (g : F)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_exists_etaleCoordinate_residueChar_localRing_of_mem_smoothLocus_of_isDiscreteValuationRing.solution
