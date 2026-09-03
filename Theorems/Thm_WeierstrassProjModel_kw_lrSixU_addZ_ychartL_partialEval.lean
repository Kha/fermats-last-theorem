import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lrSixU_addZ_ychartL_partialEval

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
theorem WeierstrassProjModel.kw_lrSixU_addZ_ychartL_partialEval (j : Fin 3) :
    ∃ (φ : ((𝒜 1) ⊗[R] (𝒜 j)) →+* (𝒜 j)),
      φ (kw_lrSixU W 1 j (.inl 2)) = -(kw_lrChart_gen W j 2) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_lrSixU_addZ_ychartL_partialEval.solution
