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
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_sub_verschiebungInt_and_isIsogenyOfHeight_of_hasStructureConstants_edgeConstants
attribute [-instance] CerednikDrinfeld.GradedCartierModuleData.module CerednikDrinfeld.GradedCartierModuleData.addCommGroup CerednikDrinfeld.GradedCartierModuleData.instModuleWittVectorSigma CerednikDrinfeld.GradedCartierModuleData.instAddCommGroupSigma MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType
attribute [-simp] CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_homothety_apply CerednikDrinfeld.FormalODModule.mem_gradedSubmodule_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_frobenius_apply CerednikDrinfeld.FormalODModule.varpiLinear_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_varpi_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply CerednikDrinfeld.FormalODModule.gradedSubmodule_toAddSubgroup MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ
attribute [-simp] MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup open MvFormalGroup.CartierModule hiding exists_hom_forall_map_eq_of_algebra_padicInt existsUnique_addMonoidHom_apply_eq_of_frobenius_expansion

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.exists_hom_map_eq_sub_verschiebungInt_and_isIsogenyOfHeight_of_hasStructureConstants_edgeConstants
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    (j : Zp2 p →+* EdgeFamily.edgeRingCharP p k)
    (Y X : FormalODModule p (EdgeFamily.edgeRingCharP p k))
    (hYs : Y.IsSpecial j) (hY4 : Y.HasHeight 4) (hXs : X.IsSpecial j) (hX4 : X.HasHeight 4)
    (δ : Fin 2 → CartierModule p Y.F) (hδ : Y.IsHomogeneousVBasis j δ)
    (hδa : Y.HasStructureConstants δ (EdgeFamily.edgeConstants p (0 : EdgeFamily.edgeRingCharP p k) 0))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hγa : X.HasStructureConstants γ (EdgeFamily.edgeRingConstants p k)) :
    ∃ ρ : FormalODModule.Hom Y X,
      CartierModule.map ρ.toLawHom (δ 0) =
          (p : WittVector p (EdgeFamily.edgeRingCharP p k)) • γ 0 -
            verschiebungInt (WittVector.teichmuller p (EdgeFamily.edgeRingCharP.η p k ^ p ^ 2) • γ 1) ∧
      CartierModule.map ρ.toLawHom (δ 1) =
          (p : WittVector p (EdgeFamily.edgeRingCharP p k)) • γ 1 -
            verschiebungInt (WittVector.teichmuller p (EdgeFamily.edgeRingCharP.ξ p k ^ p ^ 2) • γ 0) ∧
      Y.IsIsogenyOfHeight X ρ.toSeries 4 := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_hom_map_eq_sub_verschiebungInt_and_isIsogenyOfHeight_of_hasStructureConstants_edgeConstants.solution
