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
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_eq_smul_of_isEtaSection_smul_of_isEtaSection_of_isAlgClosed_of_exists_isCanonicalLMap
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_eq_smul_of_isEtaSection_smul_of_isEtaSection_of_isAlgClosed_of_exists_isCanonicalLMap
    (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    (Φ : FormalODModule p (O ⧸ pIdeal p O))
    (hΦ : Φ.IsSpecial (Rigidified.jbar ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    (hLΦ : ∃ L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod,
      (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {K : Type} [Field K] [IsAlgClosed K] [Algebra ℤ_[p] K] (ψ : O →+* K)
    (hK : IsNilpotent (p : K))
    (t : Rigidified p Φ K) (ht : t.IsAdmissible ι ψ)
    (i : Fin 2) (v : Fin 2 → ℚ_[p])
    (f₁ : K) (hf₁ : f₁ ≠ 0) (hc₁ : t.IsGradedS ι ψ (Rigidified.awayHom f₁))
    (hcb₁ : t.IsGradedSbar ι ψ (Rigidified.awayHom f₁)) (hcΦ₁ : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f₁))
    (L₁ : ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).M →+ ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).NMod)
    (hL₁ : ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).IsCanonicalLMap L₁)
    (z₁ : _) (hz₁ : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f₁) hc₁ hcb₁ hcΦ₁ L₁ hL₁ i z₁
      (algebraMap ℤ_[p] ℚ_[p] (p : ℤ_[p]) • v))
    (f₂ : K) (hf₂ : f₂ ≠ 0) (hc₂ : t.IsGradedS ι ψ (Rigidified.awayHom f₂))
    (hcb₂ : t.IsGradedSbar ι ψ (Rigidified.awayHom f₂)) (hcΦ₂ : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ (Rigidified.awayHom f₂))
    (L₂ : ((t.XS (Rigidified.awayHom f₂)).toGradedCartierModuleData _ hc₂).M →+ ((t.XS (Rigidified.awayHom f₂)).toGradedCartierModuleData _ hc₂).NMod)
    (hL₂ : ((t.XS (Rigidified.awayHom f₂)).toGradedCartierModuleData _ hc₂).IsCanonicalLMap L₂)
    (z₂ : _) (hz₂ : t.IsEtaSection ι hcΦ rΦ ψ ht.2.2.1 (Rigidified.awayHom f₂) hc₂ hcb₂ hcΦ₂ L₂ hL₂ i z₂ v) :
    ∃ y ∈ ((t.XS (Rigidified.awayHom f₁)).toGradedCartierModuleData _ hc₁).etaPiece L₁ hL₁.isCartierLMap.map_verschiebung i,
      z₁ = p • y := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_eq_smul_of_isEtaSection_smul_of_isEtaSection_of_isAlgClosed_of_exists_isCanonicalLMap.solution
