import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq
attribute [-instance] instTopologicallyFGOfFiniteType MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem CerednikDrinfeld.SpecialFormal.Rigidified.exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι))
    (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0)
      (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+
        (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ
        ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L
          hL.isCartierLMap.map_verschiebung 0 : Set _))
    {B : Type} [CommRing B] (ψ : WittVector p k →+* B)
    (t' : Rigidified p Φ B) (ht' : t'.IsAdmissible ι ψ)
    {S : Type} [CommRing S] (g : B →+* S)
    (hcb' : t'.IsGradedSbar ι ψ g) (hcΦg : Rigidified.IsGradedPhiS (Φ := Φ) ι ψ g)
    (f₁ f₂ : MvFormalGroup.CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g).F →+
      MvFormalGroup.CartierModule p (t'.XbarS g).F)
    (hW₁ : ∀ (w : WittVector p (S ⧸ pIdeal p S)) (x : MvFormalGroup.CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g).F),
      f₁ (w • x) = w • f₁ x)
    (hW₂ : ∀ (w : WittVector p (S ⧸ pIdeal p S)) (x : MvFormalGroup.CartierModule p (Rigidified.PhibarS (Φ := Φ) ψ g).F),
      f₂ (w • x) = w • f₂ x)
    (hV₁ : ∀ x, f₁ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).verschiebung x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').verschiebung (f₁ x))
    (hPi₁ : ∀ x, f₁ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).varpi x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').varpi (f₁ x))
    (hV₂ : ∀ x, f₂ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).verschiebung x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').verschiebung (f₂ x))
    (hPi₂ : ∀ x, f₂ (((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).varpi x) = ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb').varpi (f₂ x))
    (e₁ e₂ : ℕ)
    (hgen : ∀ i : Fin 2,
      e₁ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₁ hV₁ hPi₁
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
            (Rigidified.bcPhi (Φ := Φ) ψ g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g) (rΦ (Pi.single i 1))) =
        e₂ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₂ hV₂ hPi₂
          ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMap ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg)
            (Rigidified.bcPhi (Φ := Φ) ψ g) (Rigidified.bcPhi_verschiebungInt (Φ := Φ) ψ g)
            (Rigidified.bcPhi_endAct_varpiEnd (Φ := Φ) ψ g) (rΦ (Pi.single i 1)))) :
    ∃ a : ℕ, ∀ z : ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).NMod,
      p ^ a • (e₁ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₁ hV₁ hPi₁ z) =
        p ^ a • (e₂ • ((Rigidified.PhibarS (Φ := Φ) ψ g).toGradedCartierModuleData (Rigidified.jPhiS ι ψ g) hcΦg).nMap ((t'.XbarS g).toGradedCartierModuleData (Rigidified.jSbar ι ψ g) hcb') f₂ hV₂ hPi₂ z) := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_SpecialFormal_Rigidified_exists_nsmul_nMap_eq_of_forall_nMap_bcPhi_single_eq.solution
