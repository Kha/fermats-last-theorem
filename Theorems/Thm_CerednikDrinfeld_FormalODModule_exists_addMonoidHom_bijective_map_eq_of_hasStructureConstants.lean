import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem CerednikDrinfeld.FormalODModule.exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (hsep : IsHausdorff (Ideal.span {(p : B)}) B)
    (X X' : CerednikDrinfeld.FormalODModule p B)
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F)
    (γ' : Fin 2 → MvFormalGroup.CartierModule p X'.F)
    (hγ : X.IsHomogeneousVBasis j γ) (hγ' : X'.IsHomogeneousVBasis j γ')
    (a : ℕ → Fin 2 → B)
    (ha : X.HasStructureConstants γ a) (ha' : X'.HasStructureConstants γ' a) :
    ∃ θ : MvFormalGroup.CartierModule p X.F →+ MvFormalGroup.CartierModule p X'.F,
      Function.Bijective θ ∧ (∀ i : Fin 2, θ (γ i) = γ' i) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.frobenius f) =
        MvFormalGroup.CartierModule.frobenius (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.verschiebungInt f) =
        MvFormalGroup.CartierModule.verschiebungInt (θ f)) ∧
      (∀ (b : B) f, θ (MvFormalGroup.CartierModule.homothety b f) =
        MvFormalGroup.CartierModule.homothety b (θ f)) ∧
      (∀ (c : CerednikDrinfeld.Zp2 p) f,
        θ (MvFormalGroup.CartierModule.endAct (X.actEnd c) f) =
          MvFormalGroup.CartierModule.endAct (X'.actEnd c) (θ f)) ∧
      (∀ f, θ (MvFormalGroup.CartierModule.endAct X.varpiEnd f) =
        MvFormalGroup.CartierModule.endAct X'.varpiEnd (θ f)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_addMonoidHom_bijective_map_eq_of_hasStructureConstants.solution
