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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt

set_option autoImplicit false

theorem CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar
    (p : ℕ) [Fact p.Prime] :
    ∃ (X : CerednikDrinfeld.FormalODModule p
          (CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1)))
      (γ : Fin 2 → MvFormalGroup.CartierModule p X.F),
      X.IsHomogeneousVBasis
          (algebraMap (CerednikDrinfeld.Zp2 p)
            (CerednikDrinfeld.CartierLift.LiftRing p (CerednikDrinfeld.Zp2 p) ((0, 0) : ℕ × Fin 2) (0, 1))) γ ∧
        X.HasStructureConstants γ
          (fun m i => CerednikDrinfeld.CartierLift.liftVar (p := p) (R := CerednikDrinfeld.Zp2 p)
            ((0, 0) : ℕ × Fin 2) (0, 1) (m, i)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_and_hasStructureConstants_liftVar.solution
