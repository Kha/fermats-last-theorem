import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_SemistableModel_exists_maximalIdeal_stalk_eq_span_pair_of_mem_smoothLocus_of_isDiscreteValuationRing

set_option autoImplicit false

p2m_open "AlgebraicCurve IsLocalRing~exists_ofList_pair_eq_maximalIdeal_and_isRegular_of_isDiscreteValuationRing_quotient CategoryTheory AlgebraicGeometry"

theorem AlgebraicCurve.SemistableModel.exists_maximalIdeal_stalk_eq_span_pair_of_mem_smoothLocus_of_isDiscreteValuationRing
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
    let c : A →+* X.presheaf.stalk x :=
      (X.presheaf.germ ⊤ x trivial).hom.comp (toBase.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    IsDomain (X.presheaf.stalk x) ∧
    c.FormallySmooth ∧ c.EssFiniteType ∧
    Function.Surjective ((IsLocalRing.residue (X.presheaf.stalk x)).comp c) ∧
    ∃ t : X.presheaf.stalk x,
      maximalIdeal (X.presheaf.stalk x) = Ideal.span {c ϖ, t} ∧ t ∉ Ideal.span {c ϖ} := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_SemistableModel_exists_maximalIdeal_stalk_eq_span_pair_of_mem_smoothLocus_of_isDiscreteValuationRing.solution
