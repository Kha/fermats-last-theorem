import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_chartEval_equation_and_apply_self_eq_one

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

universe u
attribute [local instance] MvPolynomial.gradedAlgebra WeierstrassProjModel.kw_pbac_awayAlgebra in
theorem WeierstrassProjModel.chartEval_equation_and_apply_self_eq_one
    {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    (F : Type u) [Field F] [Algebra R F] (i : Fin 3)
    (ψ : (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
          (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
            (MvPolynomial.X i : MvPolynomial (Fin 3) R))) →ₐ[R] F) :
    (kw_lrApt_WF W F).Equation (kw_lrApt_chartEval W F i ψ)
    ∧ kw_lrApt_chartEval W F i ψ i = 1 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_chartEval_equation_and_apply_self_eq_one.solution
