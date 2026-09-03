import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import P2M.Util
import P2M.Sol.S_MvFormalGroup_WittLaw_coeff_subst_verFam_frobPolyFam_teichFam_of_coeff_eq_ghost

set_option autoImplicit false

universe u

theorem MvFormalGroup.WittLaw.coeff_subst_verFam_frobPolyFam_teichFam_of_coeff_eq_ghost
    (p : ℕ) [Fact p.Prime] {R : Type u} [CommRing R] (c : ℕ → R) (G : MvPowerSeries ℕ R)
    (hG : ∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n)) G : R) = (p : R) ^ k * c (k + n))
    (hG' : ∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) → (MvPowerSeries.coeff e G : R) = 0) :
    ((∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n))
          (MvPowerSeries.subst (MvFormalGroup.WittLaw.verFam R) G) : R) = (p : R) ^ k * ((p : R) * c (k + n + 1))) ∧
      (∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
          (MvPowerSeries.coeff e (MvPowerSeries.subst (MvFormalGroup.WittLaw.verFam R) G) : R) = 0)) ∧
    ((∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n))
          (MvPowerSeries.subst (MvFormalGroup.WittLaw.frobPolyFam p R) G) : R) =
            (p : R) ^ k * (if k + n = 0 then 0 else c (k + n - 1))) ∧
      (∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
          (MvPowerSeries.coeff e (MvPowerSeries.subst (MvFormalGroup.WittLaw.frobPolyFam p R) G) : R) = 0)) ∧
    (∀ a : R,
      (∀ k n : ℕ, (MvPowerSeries.coeff (Finsupp.single k (p ^ n))
          (MvPowerSeries.subst (MvFormalGroup.WittLaw.teichFam p a) G) : R) = (p : R) ^ k * (a ^ p ^ (k + n) * c (k + n))) ∧
      (∀ e : ℕ →₀ ℕ, (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
          (MvPowerSeries.coeff e (MvPowerSeries.subst (MvFormalGroup.WittLaw.teichFam p a) G) : R) = 0)) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_WittLaw_coeff_subst_verFam_frobPolyFam_teichFam_of_coeff_eq_ghost.solution
