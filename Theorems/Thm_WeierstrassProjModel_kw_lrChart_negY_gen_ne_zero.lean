import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lrChart_negY_gen_ne_zero

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra WeierstrassProjModel
open MvPolynomial WeierstrassCurve HomogeneousLocalization
open scoped TensorProduct

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] WeierstrassProjModel.kw_pbac_awayAlgebra

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))
theorem WeierstrassProjModel.kw_lrChart_negY_gen_ne_zero
    [IsDomain R] [W.IsElliptic] :
    (2 : (𝒜 (2 : Fin 3))) * kw_lrChart_gen W 2 1
      + (algebraMap R (𝒜 (2 : Fin 3)) W.a₁) * kw_lrChart_gen W 2 0
      + algebraMap R (𝒜 (2 : Fin 3)) W.a₃ ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_lrChart_negY_gen_ne_zero.solution
