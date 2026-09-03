import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import P2M.Util
import P2M.Sol.S_MvFormalGroup_WittLaw_subst_addFam_eq_add_of_coeff_eq_ghost

set_option autoImplicit false

universe u

theorem MvFormalGroup.WittLaw.subst_addFam_eq_add_of_coeff_eq_ghost
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] (c : ℕ → R) (G : MvPowerSeries ℕ R)
    (hG : ∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n)) G : R) = (p : R) ^ k * c (k + n))
    (hG' : ∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) → (MvPowerSeries.coeff e G : R) = 0) :
    MvPowerSeries.subst (MvFormalGroup.WittLaw.addFam p R) G =
      MvPowerSeries.subst (fun m => (MvPowerSeries.X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) G +
        MvPowerSeries.subst (fun m => (MvPowerSeries.X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) G := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_WittLaw_subst_addFam_eq_add_of_coeff_eq_ghost.solution
