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
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B)
    (i : Fin 2) (f : B) (hc : t.IsGradedS ι ψ (Rigidified.awayHom f))
    (L : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).M →+ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (z : ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung i)
    (x : PrimeSpectrum B)

    {S : Type} [CommRing S] (q : Rigidified.Baway f →+* S) (hq : Function.Surjective q) (hqI : IsNilpotent (RingHom.ker q))
    (hcS : t.IsGradedS ι ψ (q.comp (Rigidified.awayHom f)))
    (LS : ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).M →+ ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).NMod) (hLS : ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).IsCanonicalLMap LS)
    (hXS : (t.XS (Rigidified.awayHom f)).F.map q = (t.XS (q.comp (Rigidified.awayHom f))).F)
    (hSV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXS (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXS m))
    (hSP : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXS (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXS m))
    (xS : PrimeSpectrum S) (hxS : Ideal.comap (q.comp (Rigidified.awayHom f)) xS.asIdeal = x.asIdeal)

    (hred : ∃ (f₀' : S) (_ : f₀' ∉ xS.asIdeal) (hc₀' : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f))))
      (L₀' : ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').M →+ ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').NMod) (hL₀' : ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').IsCanonicalLMap L₀')
      (hXr' : (t.XS (q.comp (Rigidified.awayHom f))).F.map (algebraMap S (Localization.Away f₀')) = (t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).F)
      (hrV' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr' (((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr' m))
      (hrPi' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr' (((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr' m))
      (z₀' : ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').NMod),
      z₀' ∈ ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀').etaPiece L₀' hL₀'.isCartierLMap.map_verschiebung i ∧
        p • z₀' = ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS).nMap ((t.XS ((algebraMap S (Localization.Away f₀')).comp (q.comp (Rigidified.awayHom f)))).toGradedCartierModuleData _ hc₀') (MvFormalGroup.CartierModule.baseChangeEq _ hXr') hrV' hrPi'
          (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nMap ((t.XS (q.comp (Rigidified.awayHom f))).toGradedCartierModuleData _ hcS) (MvFormalGroup.CartierModule.baseChangeEq _ hXS) hSV hSP z)) :
    ∃ (f₀ : B) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ (Rigidified.awayHom (f * f₀)))
      (L₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).M →+ ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS (Rigidified.awayHom f)).F.map (IsLocalization.Away.awayToAwayRight f f₀ : Rigidified.Baway f →+* Rigidified.Baway (f * f₀)) = (t.XS (Rigidified.awayHom (f * f₀))).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung i ∧
        p • z₀ = ((t.XS (Rigidified.awayHom f)).toGradedCartierModuleData _ hc).nMap ((t.XS (Rigidified.awayHom (f * f₀))).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_exists_smul_eq_nMap_nMap_of_surjective_of_isNilpotent_ker.solution
