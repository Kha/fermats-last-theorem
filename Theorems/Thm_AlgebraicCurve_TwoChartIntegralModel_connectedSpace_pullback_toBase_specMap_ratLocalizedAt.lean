import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import P2M.Util
import P2M.Sol.S_AlgebraicCurve_TwoChartIntegralModel_connectedSpace_pullback_toBase_specMap_ratLocalizedAt

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve

theorem AlgebraicCurve.TwoChartIntegralModel.connectedSpace_pullback_toBase_specMap_ratLocalizedAt
    (ℓ : ℕ) [Fact ℓ.Prime] (F : Type) [Field F] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) F] (j : F) [Fact (j ≠ 0)]
    (hconst : ∀ x : F, x ∈ TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt ℓ) F j →
      x ∈ TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt ℓ) F j →
      ∃ r : ↥(GaloisRep.ratLocalizedAt ℓ), algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) F r = x)
    (hfin : Module.Finite ↥(GaloisRep.ratLocalizedAt ℓ)
      (↥(TwoChartIntegralModel.chartAlgMid ↥(GaloisRep.ratLocalizedAt ℓ) F j) ⧸
        (LinearMap.range (TwoChartIntegralModel.inclFin ↥(GaloisRep.ratLocalizedAt ℓ) F j).toLinearMap ⊔
          LinearMap.range (TwoChartIntegralModel.inclInf ↥(GaloisRep.ratLocalizedAt ℓ) F j).toLinearMap)))
    (hsec : ∃ s : Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)) ⟶ TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt ℓ) F j,
      s ≫ TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt ℓ) F j = 𝟙 _)
    (L : Type) [Field L] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) L] :
    ConnectedSpace ↥(pullback (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt ℓ) F j)
      (Scheme.TwoAffineOpenCover.specMap ↥(GaloisRep.ratLocalizedAt ℓ) L)) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_TwoChartIntegralModel_connectedSpace_pullback_toBase_specMap_ratLocalizedAt.solution
