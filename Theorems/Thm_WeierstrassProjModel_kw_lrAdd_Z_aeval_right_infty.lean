import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lrAdd_Z_aeval_right_infty

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
theorem WeierstrassProjModel.kw_lrAdd_Z_aeval_right_infty
    {A : Type u} [CommRing A] [Algebra R A] (P : Fin 3 → A) :
    MvPolynomial.aeval (R := R) (Sum.elim P ![(0:A), 1, 0]) (kw_lrAdd_Z W)
      = P 2 ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_lrAdd_Z_aeval_right_infty.solution
