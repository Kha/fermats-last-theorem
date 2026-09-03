import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_sixU_toE_over
import Theorems.Thm_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_exists_lrSixU_ne_zero_of_isElliptic
import Theorems.Thm_WeierstrassProjModel_kw_pcmpin_chartIso_inv_cover_fst_over
import Theorems.Thm_WeierstrassProjModel_kw_lrSixU_locMap_isSchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import P2M.Util
namespace P2MW.S_WeierstrassProjModel_perChart_addMorphism_pin_over

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

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

theorem solution [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (pcm : ∀ (i j : Fin 3),
      Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) ⟶ projModelCR W.toProjective)
    (hpin : ∀ (i j : Fin 3) (l : Fin 3 ⊕ Fin 3),
      kw_lrSixU_locMap W i j l ≫ pcm i j = kw_lrSixU_toE W i j l)
    (ij : Fin 3 × Fin 3) :
    (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom
        ≫ pcm ij.1 ij.2 ≫ projModelStrCR W.toProjective
      = (kwProjPullbackOpenCoverCR R W.toProjective).f ij
          ≫ pullback.fst (projModelStrCR W.toProjective) (projModelStrCR W.toProjective)
          ≫ projModelStrCR W.toProjective := by

  rw [← cancel_epi (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).inv,
    Iso.inv_hom_id_assoc]
  refine Eq.trans ?_ (kw_pcmpin_chartIso_inv_cover_fst_over W ij).symm

  haveI : IsDomain ((𝒜 ij.1) ⊗[R] (𝒜 ij.2)) := isDomain_chartTensor_of_isElliptic W ij.1 ij.2
  obtain ⟨l, hl⟩ := exists_lrSixU_ne_zero_of_isElliptic W ij.1 ij.2
  haveI : IsSchemeTheoreticallyDominant (kw_lrSixU_locMap W ij.1 ij.2 l) :=
    kw_lrSixU_locMap_isSchemeTheoreticallyDominant W ij.1 ij.2 l hl
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated
    (terminal.from (Spec (CommRingCat.of R))) (Subsingleton.elim _ _)
    (kw_lrSixU_locMap W ij.1 ij.2 l) ?_

  refine Eq.trans (Eq.trans (Category.assoc _ _ _).symm
    (congrArg (· ≫ projModelStrCR W.toProjective) (hpin ij.1 ij.2 l))) ?_
  exact sixU_toE_over W ij.1 ij.2 l

end
