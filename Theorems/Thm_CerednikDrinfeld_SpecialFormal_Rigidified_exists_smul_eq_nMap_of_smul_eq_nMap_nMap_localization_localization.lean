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
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_localization_localization
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_smul_eq_nMap_of_smul_eq_nMap_nMap_localization_localization
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    {B : Type} [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : O →+* B) (hB : IsNilpotent (p : B))
    (t : Rigidified p Φ B) (ht : t.IsAdmissible ι ψ)
    {S : Type} [CommRing S] [IsNoetherianRing S] (g : B →+* S) (hS : (p : S) = 0)
    (hc : t.IsGradedS ι ψ g)
    (L : ((t.XS g).toGradedCartierModuleData _ hc).M →+ ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hL : ((t.XS g).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
    (j : Fin 2)
    (z : ((t.XS g).toGradedCartierModuleData _ hc).NMod) (hz : z ∈ ((t.XS g).toGradedCartierModuleData _ hc).etaPiece L hL.isCartierLMap.map_verschiebung j)
    (x : PrimeSpectrum S)
    (f₀ : S) (hf₀ : f₀ ∉ x.asIdeal)
    (hc₁ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g))
    (hX₁ : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F)
    (hV₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁ (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
      ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₁ m))
    (hP₁ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₁ (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
      ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₁ m))
    (x₁ : PrimeSpectrum (Localization.Away f₀)) (hx₁ : x₁.asIdeal.comap (algebraMap S (Localization.Away f₀)) = x.asIdeal)
    (f₁ : (Localization.Away f₀)) (hf₁ : f₁ ∉ x₁.asIdeal)
    (hc₂ : t.IsGradedS ι ψ ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g)))
    (L₂ : ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).M →+ ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).NMod) (hL₂ : ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).IsCanonicalLMap L₂)
    (hX₂ : (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F.map (algebraMap (Localization.Away f₀) (Localization.Away f₁)) = (t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).F)
    (hV₂ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₂ (((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁).verschiebung m) =
      ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hX₂ m))
    (hP₂ : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hX₂ (((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁).varpi m) =
      ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hX₂ m))
    (z₂ : ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).NMod) (hz₂ : z₂ ∈ ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂).etaPiece L₂ hL₂.isCartierLMap.map_verschiebung j)
    (heq : p • z₂ = ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁).nMap ((t.XS ((algebraMap (Localization.Away f₀) (Localization.Away f₁)).comp ((algebraMap S (Localization.Away f₀)).comp g))).toGradedCartierModuleData _ hc₂) (MvFormalGroup.CartierModule.baseChangeEq _ hX₂) hV₂ hP₂
      (((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₁) (MvFormalGroup.CartierModule.baseChangeEq _ hX₁) hV₁ hP₁ z)) :
    ∃ (f₀ : S) (_ : f₀ ∉ x.asIdeal) (hc₀ : t.IsGradedS ι ψ ((algebraMap S (Localization.Away f₀)).comp g))
      (L₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).M →+ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod) (hL₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).IsCanonicalLMap L₀)
      (hXr : (t.XS g).F.map (algebraMap S (Localization.Away f₀)) = (t.XS ((algebraMap S (Localization.Away f₀)).comp g)).F)
      (hrV : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).verschiebung m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).verschiebung (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (hrPi : ∀ m, MvFormalGroup.CartierModule.baseChangeEq _ hXr (((t.XS g).toGradedCartierModuleData _ hc).varpi m) =
        ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).varpi (MvFormalGroup.CartierModule.baseChangeEq _ hXr m))
      (z₀ : ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).NMod),
      z₀ ∈ ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀).etaPiece L₀ hL₀.isCartierLMap.map_verschiebung j ∧
        p • z₀ = ((t.XS g).toGradedCartierModuleData _ hc).nMap ((t.XS ((algebraMap S (Localization.Away f₀)).comp g)).toGradedCartierModuleData _ hc₀) (MvFormalGroup.CartierModule.baseChangeEq _ hXr) hrV hrPi z := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_smul_eq_nMap_of_smul_eq_nMap_nMap_localization_localization.solution
