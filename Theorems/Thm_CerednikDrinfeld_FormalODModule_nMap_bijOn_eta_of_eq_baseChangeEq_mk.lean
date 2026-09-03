import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_nMap_bijOn_eta_of_eq_baseChangeEq_mk
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega
  MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem CerednikDrinfeld.FormalODModule.nMap_bijOn_eta_of_eq_baseChangeEq_mk
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (hS : IsNilpotent (p : S))
    (j : Zp2 p →+* S) (X : FormalODModule p S)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (Xb : FormalODModule p (S ⧸ pIdeal p S)) (hXb : X.map (Ideal.Quotient.mk (pIdeal p S)) = Xb)
    (jb : Zp2 p →+* S ⧸ pIdeal p S) (hjb : (Ideal.Quotient.mk (pIdeal p S)).comp j = jb)
    (hcb : IsCompl (Xb.gradedPiece jb 0) (Xb.gradedPiece jb 1))
    (hF : X.F.map (Ideal.Quotient.mk (pIdeal p S)) = Xb.F)
    (red : CartierModule p X.F →+ CartierModule p Xb.F)
    (hred : red = CartierModule.baseChangeEq (Ideal.Quotient.mk (pIdeal p S)) hF)
    (hredV : ∀ x, red ((X.toGradedCartierModuleData j hc).verschiebung x) =
      (Xb.toGradedCartierModuleData jb hcb).verschiebung (red x))
    (hredPi : ∀ x, red ((X.toGradedCartierModuleData j hc).varpi x) =
      (Xb.toGradedCartierModuleData jb hcb).varpi (red x))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (Lb : (Xb.toGradedCartierModuleData jb hcb).M →+ (Xb.toGradedCartierModuleData jb hcb).NMod)
    (hLb : (Xb.toGradedCartierModuleData jb hcb).IsCanonicalLMap Lb)
    (hLL : ∀ x, Lb (red x) =
      (X.toGradedCartierModuleData j hc).nMap (Xb.toGradedCartierModuleData jb hcb) red hredV hredPi (L x)) :
    Set.BijOn ((X.toGradedCartierModuleData j hc).nMap (Xb.toGradedCartierModuleData jb hcb) red hredV hredPi)
      ((X.toGradedCartierModuleData j hc).eta L hL.isCartierLMap.map_verschiebung : Set _)
      ((Xb.toGradedCartierModuleData jb hcb).eta Lb hLb.isCartierLMap.map_verschiebung : Set _) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_nMap_bijOn_eta_of_eq_baseChangeEq_mk.solution
