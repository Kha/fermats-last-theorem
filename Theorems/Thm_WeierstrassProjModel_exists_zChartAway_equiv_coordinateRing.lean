import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing
attribute [-instance] WeierstrassProjModel.quotGradingSubmoduleDegreeZeroFiniteType WeierstrassProjModel.kw_lrChart_tensorCommRing WeierstrassProjModel.kw_lrChart_biGrading_gradedAlgebra WeierstrassProjModel.projModel_isIso_spec_mapCR WeierstrassProjModel.kw_lrSymOC_isDomain_ℬ₀ WeierstrassProjModel.isProper_projModelStrCR WeierstrassProjModel.homogeneousSubmoduleDegreeZeroFiniteType
attribute [-simp] WeierstrassProjModel.kw_lrAdd_substHom_X WeierstrassProjModel.kw_lrSym_substHom_X

universe u
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem WeierstrassProjModel.exists_zChartAway_equiv_coordinateRing
    {R : Type u} [CommRing R] (V : WeierstrassCurve.Projective R) :
    ∃ f : HomogeneousLocalization.Away (WeierstrassProjModel.projModelGradingCR V)
          (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
            (MvPolynomial.X 2 : MvPolynomial (Fin 3) R)) →+*
        (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}),
      Function.Bijective f ∧
      f.comp ((HomogeneousLocalization.fromZeroRingHom (WeierstrassProjModel.projModelGradingCR V)
            (Submonoid.powers (Ideal.Quotient.mk
              (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal
              (MvPolynomial.X 2 : MvPolynomial (Fin 3) R)))).comp
          (algebraMap R (WeierstrassProjModel.projModelGradingCR V 0)))
        = algebraMap R (Polynomial (Polynomial R) ⧸ Ideal.span {V.toAffine.polynomial}) ∧
      ∀ (n : ℕ) (b : MvPolynomial (Fin 3) R)
        (hb : b ∈ MvPolynomial.homogeneousSubmodule (Fin 3) R (n • 1)),
        f (HomogeneousLocalization.Away.mk (WeierstrassProjModel.projModelGradingCR V)
            (HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _
              ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R 2)))
            n
            (Ideal.Quotient.mk (WeierstrassProjModel.projModelHomogeneousIdealCR V).toIdeal b)
            (HomogeneousIdealQuotientGrading.mk_mem_quotGradingSubmodule _ _ hb))
          = Ideal.Quotient.mk _
              (MvPolynomial.aeval
                (![Polynomial.C Polynomial.X, Polynomial.X, 1] : Fin 3 → Polynomial (Polynomial R)) b) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_exists_zChartAway_equiv_coordinateRing.solution
