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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_eq_zero_of_forall_nMap_baseChange_eq_zero
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega
  MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

theorem CerednikDrinfeld.FormalODModule.eq_zero_of_forall_nMap_baseChange_eq_zero
    (p : ℕ) [Fact p.Prime] {S : Type} [CommRing S] (j : Zp2 p →+* S) (X : FormalODModule p S)
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    {ι : Type} (K : ι → Type) [∀ α, CommRing (K α)] (φ : ∀ α, S →+* K α)
    (hinj : ∀ s : S, (∀ α, φ α s = 0) → s = 0)
    (hcK : ∀ α, IsCompl ((X.map (φ α)).gradedPiece ((φ α).comp j) 0) ((X.map (φ α)).gradedPiece ((φ α).comp j) 1))
    (bc : ∀ α, CartierModule p X.F →+ CartierModule p (X.map (φ α)).F)
    (hbc : ∀ α, bc α = CartierModule.baseChange (φ α))
    (hbcV : ∀ α x, bc α ((X.toGradedCartierModuleData j hc).verschiebung x) = ((X.map (φ α)).toGradedCartierModuleData ((φ α).comp j) (hcK α)).verschiebung (bc α x))
    (hbcPi : ∀ α x, bc α ((X.toGradedCartierModuleData j hc).varpi x) = ((X.map (φ α)).toGradedCartierModuleData ((φ α).comp j) (hcK α)).varpi (bc α x))
    (z : (X.toGradedCartierModuleData j hc).NMod)
    (hz : ∀ α, (X.toGradedCartierModuleData j hc).nMap ((X.map (φ α)).toGradedCartierModuleData ((φ α).comp j) (hcK α)) (bc α) (hbcV α) (hbcPi α) z = 0) :
    z = 0 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_eq_zero_of_forall_nMap_baseChange_eq_zero.solution
