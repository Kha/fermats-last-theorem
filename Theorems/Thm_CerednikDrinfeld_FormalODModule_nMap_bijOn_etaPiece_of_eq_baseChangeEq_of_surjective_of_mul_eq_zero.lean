import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_nMap_bijOn_etaPiece_of_eq_baseChangeEq_of_surjective_of_mul_eq_zero
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

theorem CerednikDrinfeld.FormalODModule.nMap_bijOn_etaPiece_of_eq_baseChangeEq_of_surjective_of_mul_eq_zero
    (p : ℕ) [Fact p.Prime] {S S' : Type} [CommRing S] [CommRing S'] (hS : IsNilpotent (p : S))
    (φ : S →+* S') (hφ : Function.Surjective φ) (hker : ∀ x y : S, φ x = 0 → φ y = 0 → x * y = 0)
    (j : Zp2 p →+* S) (X : FormalODModule p S)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (X' : FormalODModule p S') (hX' : X.map φ = X')
    (j' : Zp2 p →+* S') (hj' : φ.comp j = j')
    (hc' : IsCompl (X'.gradedPiece j' 0) (X'.gradedPiece j' 1))
    (hF : X.F.map φ = X'.F)
    (red : CartierModule p X.F →+ CartierModule p X'.F)
    (hred : red = CartierModule.baseChangeEq φ hF)
    (hredV : ∀ x, red ((X.toGradedCartierModuleData j hc).verschiebung x) =
      (X'.toGradedCartierModuleData j' hc').verschiebung (red x))
    (hredPi : ∀ x, red ((X.toGradedCartierModuleData j hc).varpi x) =
      (X'.toGradedCartierModuleData j' hc').varpi (red x))
    (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (L' : (X'.toGradedCartierModuleData j' hc').M →+ (X'.toGradedCartierModuleData j' hc').NMod)
    (hL' : (X'.toGradedCartierModuleData j' hc').IsCanonicalLMap L') :
    (∀ x, L' (red x) =
      (X.toGradedCartierModuleData j hc).nMap (X'.toGradedCartierModuleData j' hc') red hredV hredPi (L x)) ∧
    Set.BijOn ((X.toGradedCartierModuleData j hc).nMap (X'.toGradedCartierModuleData j' hc') red hredV hredPi)
      ((X.toGradedCartierModuleData j hc).eta L hL.isCartierLMap.map_verschiebung : Set _)
      ((X'.toGradedCartierModuleData j' hc').eta L' hL'.isCartierLMap.map_verschiebung : Set _) ∧
    ∀ i : Fin 2,
      Set.BijOn ((X.toGradedCartierModuleData j hc).nMap (X'.toGradedCartierModuleData j' hc') red hredV hredPi)
        ((X.toGradedCartierModuleData j hc).etaPiece L hL.isCartierLMap.map_verschiebung i : Set _)
        ((X'.toGradedCartierModuleData j' hc').etaPiece L' hL'.isCartierLMap.map_verschiebung i : Set _) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_nMap_bijOn_etaPiece_of_eq_baseChangeEq_of_surjective_of_mul_eq_zero.solution
