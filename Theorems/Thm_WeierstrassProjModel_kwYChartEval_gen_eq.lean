import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kwYChartEval_gen_eq

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable (R : Type u) [CommRing R] (W : WeierstrassCurve R)
theorem WeierstrassProjModel.kwYChartEval_gen_eq (m : Fin 3) :
    kwYChartEval R W (kw_lrChart_gen W 1 m) = ![(0:R), 1, 0] m := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kwYChartEval_gen_eq.solution
