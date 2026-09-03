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
import P2M.Sol.S_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt

set_option autoImplicit false

universe u

theorem MvFormalGroup.CartierModule.exists_zp2Action_of_graded_frobenius_expansion
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [Algebra (PadicInt p) B]
    (j : CerednikDrinfeld.Zp2 p →+* B)
    (Φ : MvFormalGroup 2 B) [Φ.IsComm]
    (f : Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hf : ∀ i l, MvFormalGroup.CartierModule.tangent (f i) l = if i = l then 1 else 0)
    (c : ℕ → Fin 2 → Fin 2 → B)
    (hc : ∀ (m : ℕ) (i l : Fin 2), (l : ℕ) ≠ (m + i + 1) % 2 → c m i l = 0)
    (h : ℕ → Fin 2 → MvFormalGroup.CartierModule p Φ)
    (hexp : ∀ (N : ℕ) (i : Fin 2), MvFormalGroup.CartierModule.frobenius (f i) =
      (∑ m ∈ Finset.range N, (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[m]
          (∑ l : Fin 2, MvFormalGroup.CartierModule.homothety (c m i l) (f l))) +
        (⇑(MvFormalGroup.CartierModule.verschiebungInt (p := p) (Φ := Φ)))^[N] (h N i)) :
    ∃ (θ : CerednikDrinfeld.Zp2 p →+* WittVector p (CerednikDrinfeld.Zp2 p))
      (act : CerednikDrinfeld.Zp2 p → CerednikDrinfeld.SpecialFormal.Series B)
      (hact : ∀ a, CerednikDrinfeld.SpecialFormal.IsLawHom Φ Φ (act a)),
      (∀ (a : CerednikDrinfeld.Zp2 p) (n : ℕ), WittVector.ghostComponent n (θ a) =
          (⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[n] a) ∧
      (∀ c : GaloisField p 2, θ (WittVector.teichmuller p c) =
          WittVector.teichmuller p (WittVector.teichmuller p c)) ∧
      act 1 = CerednikDrinfeld.SpecialFormal.Series.id B ∧
      (∀ a b, act (a * b) = (act a).comp (act b)) ∧
      (∀ a b, act (a + b) = CerednikDrinfeld.SpecialFormal.Series.addVia Φ (act a) (act b)) ∧
      ∀ (a : CerednikDrinfeld.Zp2 p) (i : Fin 2),
        MvFormalGroup.CartierModule.map (hact a).toHom (f i) =
          WittVector.map j (θ ((⇑(WittVector.frobenius (p := p) (R := GaloisField p 2)))^[(i : ℕ)] a)) • f i := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_CartierModule_exists_zp2Action_of_graded_frobenius_expansion.solution
