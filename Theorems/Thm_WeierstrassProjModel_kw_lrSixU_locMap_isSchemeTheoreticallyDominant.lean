import Definitions.Def_WeierstrassCurve_ProjModel_GroupLawVocabulary
import Theorems.Thm_WeierstrassProjModel_isDomain_chartTensor_of_isElliptic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import P2M.Util
import P2M.Sol.S_WeierstrassProjModel_kw_lrSixU_locMap_isSchemeTheoreticallyDominant

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
theorem WeierstrassProjModel.kw_lrSixU_locMap_isSchemeTheoreticallyDominant
    [IsDomain R] [IsNoetherianRing R] [W.IsElliptic]
    (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) (hl : kw_lrSixU W i j l ≠ 0) :
    IsSchemeTheoreticallyDominant (kw_lrSixU_locMap W i j l) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassProjModel_kw_lrSixU_locMap_isSchemeTheoreticallyDominant.solution
