import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_BigWittLaw_exists_hom_subst_pow_eq
attribute [-simp] MvPowerSeries.blockPermEmbed_apply

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.exists_hom_subst_pow_eq
    {R : Type u} [CommRing R] {d : ℕ} (Φ : MvFormalGroup d R) [Φ.IsComm]
    (γ : Fin d → PowerSeries R) (hγ : ∀ j, PowerSeries.constantCoeff (γ j) = 0) :
    ∃ G : Fin d → MvPowerSeries ℕ R,
      (∀ j, MvPowerSeries.constantCoeff (G j) = 0) ∧
      (∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
          MvPowerSeries.subst
            (Sum.elim
              (fun l => MvPowerSeries.subst
                (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
              fun l => MvPowerSeries.subst
                (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
            (Φ.toPowerSeries j)) ∧
      (∀ j, MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j) = γ j) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_BigWittLaw_exists_hom_subst_pow_eq.solution
