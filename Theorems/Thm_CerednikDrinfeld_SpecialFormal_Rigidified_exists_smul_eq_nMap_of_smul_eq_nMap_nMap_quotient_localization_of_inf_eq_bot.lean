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
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [Algebra ℤ_[p] B] (ψ : O →+* B)
    (t : Rigidified p Φ B)
    {S : Type} [CommRing S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2)
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung j)
    (x : PrimeSpectrum S)
    (J₀ J₁ : Ideal S) (hJ : J₀ ⊓ J₁ = ⊥)

    (hcq₀ : t.IsGradedS ι ψ ((Ideal.Quotient.mk J₀).comp g))
    (hXq₀ : (t.XS g).F.map (Ideal.Quotient.mk J₀) = (t.XS ((Ideal.Quotient.mk J₀).comp g)).F)
    (hVq₀ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ m))
    (hPq₀ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXq₀ m))
    (x₀' : PrimeSpectrum (S ⧸ J₀)) (hx₀' : x₀'.asIdeal.comap (Ideal.Quotient.mk J₀) = x.asIdeal)
    (f₀' : S ⧸ J₀) (hf₀' : f₀' ∉ x₀'.asIdeal)
    (hc₀' : t.IsGradedS ι ψ ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g)))
    (L₀' : ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').M →+ ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').NMod) (hL₀' : ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').IsCanonicalLMap L₀')
    (hX₀' : (t.XS ((Ideal.Quotient.mk J₀).comp g)).F.map (algebraMap (S ⧸ J₀) (Localization.Away f₀')) = (t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).F)
    (hV₀' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₀' (((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).verschiebung m) =
      ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₀' m))
    (hP₀' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₀' (((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).varpi m) =
      ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₀' m))
    (z₀' : ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').NMod) (hz₀' : z₀' ∈ ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀').etaPiece L₀' hL₀'.isCartierLMap.map_verschiebung j)
    (heq₀ : p • z₀' = ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀).nMap ((t.XS ((algebraMap (S ⧸ J₀) (Localization.Away f₀')).comp ((Ideal.Quotient.mk J₀).comp g))).toGradedCartierModuleData _ hc₀') (MvFormalGroup.CartierModule.baseChangeEq _ hX₀') hV₀' hP₀'
      (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₀).comp g)).toGradedCartierModuleData _ hcq₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXq₀) hVq₀ hPq₀ z))

    (hcq₁ : t.IsGradedS ι ψ ((Ideal.Quotient.mk J₁).comp g))
    (hXq₁ : (t.XS g).F.map (Ideal.Quotient.mk J₁) = (t.XS ((Ideal.Quotient.mk J₁).comp g)).F)
    (hVq₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ m))
    (hPq₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXq₁ m))
    (x₁' : PrimeSpectrum (S ⧸ J₁)) (hx₁' : x₁'.asIdeal.comap (Ideal.Quotient.mk J₁) = x.asIdeal)
    (f₁' : S ⧸ J₁) (hf₁' : f₁' ∉ x₁'.asIdeal)
    (hc₁' : t.IsGradedS ι ψ ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g)))
    (L₁' : ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').M →+ ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').NMod) (hL₁' : ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').IsCanonicalLMap L₁')
    (hX₁' : (t.XS ((Ideal.Quotient.mk J₁).comp g)).F.map (algebraMap (S ⧸ J₁) (Localization.Away f₁')) = (t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).F)
    (hV₁' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁' (((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).verschiebung m) =
      ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₁' m))
    (hP₁' : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁' (((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).varpi m) =
      ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₁' m))
    (z₁' : ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').NMod) (hz₁' : z₁' ∈ ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁').etaPiece L₁' hL₁'.isCartierLMap.map_verschiebung j)
    (heq₁ : p • z₁' = ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁).nMap ((t.XS ((algebraMap (S ⧸ J₁) (Localization.Away f₁')).comp ((Ideal.Quotient.mk J₁).comp g))).toGradedCartierModuleData _ hc₁') (MvFormalGroup.CartierModule.baseChangeEq _ hX₁') hV₁' hP₁'
      (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((Ideal.Quotient.mk J₁).comp g)).toGradedCartierModuleData _ hcq₁) (MvFormalGroup.CartierModule.baseChangeEq _ hXq₁) hVq₁ hPq₁ z)) :
    ∃ (f₀ : S) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g))
      (L₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j ∧
        p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_quotient_localization_of_inf_eq_bot.solution
