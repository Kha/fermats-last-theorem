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
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

theorem CerednikDrinfeld.FormalODModule.exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p]
    (j : Zp2 p →+* DualNumber κ) (X : FormalODModule p (DualNumber κ))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (a ν : ℕ → Fin 2 → κ) (c : κ)
    (hA : X.HasStructureConstants γ (fun m i => algebraMap κ (DualNumber κ) (a m i) + (c * ν m i) • DualNumber.eps))
    (hν0 : ∀ i, ν 0 i = 0) (i₀ : Fin 2) (ha0 : a 0 i₀ = 0)
    (L : (X.toGradedCartierModuleData j hc).M →+
      (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (z : (X.toGradedCartierModuleData j hc).NMod)
    (hz : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L
      hL.isCartierLMap.map_verschiebung i₀)
    (m : CartierModule p X.F)
    (hm : (X.toGradedCartierModuleData j hc).vRange.mkQ m =
      (X.toGradedCartierModuleData j hc).u L
        hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz).1⟩) :
    (∃ x : DualNumber κ, tangent m = x • tangent (γ i₀)) ∧
    ∀ x : DualNumber κ, tangent m = x • tangent (γ i₀) →
      a 0 (FormalODModule.piIndex 0 i₀) ^ p * TrivSqZeroExt.fst x =
        (a 0 (FormalODModule.piIndex 0 i₀) ^ p * a 1 i₀ + a 0 (FormalODModule.piIndex 0 i₀) * a 1 (FormalODModule.piIndex 0 i₀)) *
            TrivSqZeroExt.fst x ^ p +
        (a 0 (FormalODModule.piIndex 0 i₀) ^ (p + 1) * a 2 i₀ -
            a 0 (FormalODModule.piIndex 0 i₀) * a 1 i₀ ^ p * a 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst x ^ (p ^ 2) ∧
      a 0 (FormalODModule.piIndex 0 i₀) ^ p * TrivSqZeroExt.snd x =
        c * ((a 0 (FormalODModule.piIndex 0 i₀) ^ (p + 1) * ν 2 i₀ -
              a 0 (FormalODModule.piIndex 0 i₀) * a 1 i₀ ^ p * ν 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst x ^ (p ^ 2) +
            (a 0 (FormalODModule.piIndex 0 i₀) ^ p * ν 1 i₀ + a 0 (FormalODModule.piIndex 0 i₀) * ν 1 (FormalODModule.piIndex 0 i₀)) *
              TrivSqZeroExt.fst x ^ p) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber.solution
