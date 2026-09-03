import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadrupleRelations
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_CartierQuadrupleVia
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_baseChange_comparison
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_baseChange_comparison
    {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] (ι : Zp2 p →+* O)
    {Φ : FormalODModule p (O ⧸ pIdeal p O)}
    (hcΦ : IsCompl (Φ.gradedPiece (Rigidified.jbar ι) 0) (Φ.gradedPiece (Rigidified.jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (Rigidified.jbar ι) hcΦ).NMod)
    {B B' : Type} [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B') (f : B →+* B') (hf : f.comp ψ = ψ')
    (t : Rigidified p Φ B)
    (hOD : FormalODModule.IsODHom (t.Φbar ψ) t.Xbar t.ρ)
    (hOD' : FormalODModule.IsODHom ((t.map f).Φbar ψ') (t.map f).Xbar (t.map f).ρ)
    {S S' : Type} [CommRing S] [CommRing S'] (g : B →+* S) (g' : B' →+* S') (e : S →+* S')
    (hge : g'.comp f = e.comp g)
    (hc : t.IsGradedS ι ψ g) (hcb : t.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (hc' : (t.map f).IsGradedS ι ψ' g') (hcb' : (t.map f).IsGradedSbar ι ψ' g')
    (hcΦg' : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ' g')
    (γ : Fin 2 → MvFormalGroup.CartierModule p (t.XS g).F) (hγ : (t.XS g).IsHomogeneousVBasis (Rigidified.jS ι ψ g) γ) :
    ∃ (bc : MvFormalGroup.CartierModule p (t.XS g).F →+ MvFormalGroup.CartierModule p ((t.map f).XS g').F)
      (hbc : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' e ((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc) (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc),
      (∀ (m : MvFormalGroup.CartierModule p (t.XS g).F) (i : Fin 2),
          MvFormalGroup.CartierModule.tangent (bc m) i = e (MvFormalGroup.CartierModule.tangent m i)) ∧
      ∃ bcbar : ((t.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb).NMod →+ (((t.map (f : B →+* B')).XbarS g').toGradedCartierModuleData (Rigidified.jSbar ι ψ' g') hcb').NMod,
        (∀ z, (t.map f).etaRed ι ψ' g' hc' hcb' (((t.XS g).toGradedCartierModuleData (Rigidified.jS ι ψ g) hc).nMap (((t.map (f : B →+* B')).XS g').toGradedCartierModuleData (Rigidified.jS ι ψ' g') hc') bc hbc.2.2.1 hbc.2.2.2.1 z) =
            bcbar (t.etaRed ι ψ g hc hcb z)) ∧
        (∀ w, (t.map f).rigidNum ι hcΦ rΦ ψ' hOD' g' hcb' hcΦg' w = bcbar (t.rigidNum ι hcΦ rΦ ψ hOD g hcb hcΦg w)) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_baseChange_comparison.solution
