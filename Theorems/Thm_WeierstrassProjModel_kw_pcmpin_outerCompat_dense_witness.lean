import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_pcmpin_outerCompat_dense_witness

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
theorem WeierstrassProjModel.kw_pcmpin_outerCompat_dense_witness
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (pcm : ∀ (i j : Fin 3), Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) ⟶ projModelCR W.toProjective)
    (hpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l ≫ pcm i j = kw_lrSixU_toE W i j l)
    (ij ij' : Fin 3 × Fin 3)
    (hne : Nonempty ↥(pullback ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                               ((kwProjPullbackOpenCoverCR R W.toProjective).f ij'))) :
    ∃ (D : Scheme.{u}) (ι : D ⟶ pullback ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                                         ((kwProjPullbackOpenCoverCR R W.toProjective).f ij'))
      (_ : IsSchemeTheoreticallyDominant ι),
      ι ≫ pullback.fst ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                       ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
          ≫ (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom ≫ pcm ij.1 ij.2
        = ι ≫ pullback.snd ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                           ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
          ≫ (kwProjPullbackChartIsoCR R W.toProjective ij'.1 ij'.2).hom ≫ pcm ij'.1 ij'.2 := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_pcmpin_outerCompat_dense_witness.solution
