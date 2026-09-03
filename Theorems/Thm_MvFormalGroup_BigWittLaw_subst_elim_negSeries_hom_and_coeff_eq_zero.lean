import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_BigWittLaw_subst_elim_negSeries_hom_and_coeff_eq_zero
attribute [-instance] MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup
attribute [-simp] MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.subst_elim_negSeries_hom_and_coeff_eq_zero
    {R : Type u} [CommRing R] {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (G H : Fin d → MvPowerSeries ℕ R)
    (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0)
    (hG : ∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))
    (hH0 : ∀ j, MvPowerSeries.constantCoeff (H j) = 0)
    (hH : ∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (H j) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (H l))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (H l))
        (Φ.toPowerSeries j))
    (n : ℕ) (hn : 1 ≤ n)
    (hGn : ∀ (j : Fin d) (k : ℕ), k < n →
      PowerSeries.coeff k (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j)) = 0)
    (hHn : ∀ (j : Fin d) (k : ℕ), k < n →
      PowerSeries.coeff k (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (H j)) = 0)
    (hGH : ∀ j : Fin d,
      PowerSeries.coeff n (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j))
        = PowerSeries.coeff n (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (H j))) :
    (∀ j, MvPowerSeries.constantCoeff
        (MvPowerSeries.subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries j)) = 0) ∧
    (∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R)
        (MvPowerSeries.subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries j)) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R))
            (MvPowerSeries.subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries l)))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R))
            (MvPowerSeries.subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries l)))
        (Φ.toPowerSeries j)) ∧
    (∀ (j : Fin d) (k : ℕ), k < n + 1 →
      PowerSeries.coeff k (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1))
        (MvPowerSeries.subst (Sum.elim G (MvFormalGroup.negSeries Φ H)) (Φ.toPowerSeries j))) = 0) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_BigWittLaw_subst_elim_negSeries_hom_and_coeff_eq_zero.solution
