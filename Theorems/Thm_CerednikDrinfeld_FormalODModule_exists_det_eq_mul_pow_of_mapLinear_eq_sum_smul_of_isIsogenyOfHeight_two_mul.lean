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
import P2M.Sol.S_CerednikDrinfeld_FormalODModule_exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul
attribute [-instance] instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.FormalODModule.exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] [PerfectRing K p]
    (j : Zp2 p →+* K) (Y Z : FormalODModule p K) (hY : Y.IsSpecial j) (hZ : Z.IsSpecial j)
    (hY4 : Y.HasHeight 4) (hZ4 : Z.HasHeight 4)
    (hcY : IsCompl (Y.gradedPiece j 0) (Y.gradedPiece j 1))
    (hcZ : IsCompl (Z.gradedPiece j 0) (Z.gradedPiece j 1))
    (ρ : SpecialFormal.Series K) (h : ℕ) (hρ : FormalODModule.IsIsogenyOfHeight Y Z ρ (2 * h))
    (c : ℤ_[p] →+* WittVector p K)
    (e : Fin 2 → MvFormalGroup.CartierModule p Y.F)
    (he : ∀ m ∈ Y.gradedPiece j 0, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e r)
    (he0 : ∀ r, e r ∈ Y.gradedPiece j 0)
    (e' : Fin 2 → MvFormalGroup.CartierModule p Z.F)
    (he' : ∀ m ∈ Z.gradedPiece j 0, ∃! w : Fin 2 → WittVector p K, m = ∑ r, w r • e' r)
    (he'0 : ∀ r, e' r ∈ Z.gradedPiece j 0)
    (A : Matrix (Fin 2) (Fin 2) ℤ_[p])
    (hA : ∀ r, MvFormalGroup.CartierModule.mapLinear (p := p) hρ.1.1.toHom (e r) = ∑ s, c (A s r) • e' s) :
    ∃ u : ℤ_[p]ˣ, A.det = (u : ℤ_[p]) * (p : ℤ_[p]) ^ h := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_FormalODModule_exists_det_eq_mul_pow_of_mapLinear_eq_sum_smul_of_isIsogenyOfHeight_two_mul.solution
