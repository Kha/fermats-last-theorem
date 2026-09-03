import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_BigWittLaw_coeff_eq_zero_of_coeff_subst_pow_eq_zero

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.coeff_eq_zero_of_coeff_subst_pow_eq_zero
    {R : Type u} [CommRing R] {d : ℕ} (Φ : MvFormalGroup d R)
    (G : Fin d → MvPowerSeries ℕ R)
    (hG0 : ∀ j, MvPowerSeries.constantCoeff (G j) = 0)
    (hG : ∀ j, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (G j) =
      MvPowerSeries.subst
        (Sum.elim
          (fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
          fun l => MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (G l))
        (Φ.toPowerSeries j))
    (K : ℕ)
    (h : ∀ (j : Fin d) (n : ℕ), n < K →
      PowerSeries.coeff n (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) (G j)) = 0)
    (j : Fin d) (e : ℕ →₀ ℕ) (he : Finsupp.weight (fun m : ℕ => m + 1) e < K) :
    MvPowerSeries.coeff e (G j) = 0 := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_BigWittLaw_coeff_eq_zero_of_coeff_subst_pow_eq_zero.solution
