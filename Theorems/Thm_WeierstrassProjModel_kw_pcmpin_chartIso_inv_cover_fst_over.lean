import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_pcmpin_chartIso_inv_cover_fst_over

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
theorem WeierstrassProjModel.kw_pcmpin_chartIso_inv_cover_fst_over
    (ij : Fin 3 × Fin 3) :
    (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).inv
        ≫ (kwProjPullbackOpenCoverCR R W.toProjective).f ij
        ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
        ≫ projModelStrCR W.toProjective
      = Spec.map (CommRingCat.ofHom (algebraMap R ((𝒜 ij.1) ⊗[R] (𝒜 ij.2)))) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_pcmpin_chartIso_inv_cover_fst_over.solution
