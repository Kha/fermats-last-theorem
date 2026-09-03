import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lrSixU_addZ_ychartR_partialEval

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
theorem WeierstrassProjModel.kw_lrSixU_addZ_ychartR_partialEval (i : Fin 3) :
    ∃ (φ : ((𝒜 i) ⊗[R] (𝒜 1)) →+* (𝒜 i)),
      φ (kw_lrSixU W i 1 (.inl 2)) = (kw_lrChart_gen W i 2) ^ 2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_lrSixU_addZ_ychartR_partialEval.solution
