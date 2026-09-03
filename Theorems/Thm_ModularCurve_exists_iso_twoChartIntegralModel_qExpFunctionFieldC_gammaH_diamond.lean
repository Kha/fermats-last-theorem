import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_CohCarrier_Level
import P2M.Util
import P2M.Sol.S_ModularCurve_exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    [IsSeparated (TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)]
    (ρ : CongruenceSubgroup.Gamma0 M →* RingAut ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hρH : ∀ γ : CongruenceSubgroup.Gamma0 M, (γ : SL(2, ℤ)) ∈ CohCarrier.GammaH M H → ρ γ = 1)
    (hρ0 : ∀ (γ : CongruenceSubgroup.Gamma0 M) (x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))),
      (x : LaurentSeries ℚ) ∈ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M) → ρ γ x = x) :
    ∃ (dia : (ZMod M)ˣ →
        (TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j ≅
          TwoChartIntegralModel ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j))
      (diaFin : (ZMod M)ˣ →
        (↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)
          →ₐ[↥(GaloisRep.ratLocalizedAt p)]
          ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)))
      (diaInf : (ZMod M)ˣ →
        (↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)
          →ₐ[↥(GaloisRep.ratLocalizedAt p)]
          ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j))),
      (∀ d, (dia d).hom ≫ TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j =
        TwoChartIntegralModel.toBase ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j) ∧
      (∀ d d', (dia (d * d')).hom = (dia d).hom ≫ (dia d').hom) ∧
      (∀ d, d ∈ H → dia d = Iso.refl _) ∧
      (∀ (d : (ZMod M)ˣ) (γ : CongruenceSubgroup.Gamma0 M), (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod M) = d →
        (∀ x, ((diaFin d x : ↥(TwoChartIntegralModel.chartAlgFin ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = ρ γ x) ∧
        (∀ x, ((diaInf d x : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p)
            ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j)) : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) = ρ γ x) ∧
        Spec.map (CommRingCat.ofHom (diaFin d).toRingHom) ≫
            TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j =
          TwoChartIntegralModel.ιFin ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j ≫ (dia d).inv ∧
        Spec.map (CommRingCat.ofHom (diaInf d).toRingHom) ≫
            TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j =
          TwoChartIntegralModel.ιInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) j ≫ (dia d).inv) := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_exists_iso_twoChartIntegralModel_qExpFunctionFieldC_gammaH_diamond.solution
