import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_ArtinHasse
import P2M.Util
import P2M.Sol.S_MvFormalGroup_BigWittLaw_exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt
    (p : ℕ) [Fact p.Prime] (R : Type u) [CommRing R] [Algebra ℤ_[p] R] :
    ∃ π : ℕ → ℕ → MvPowerSeries ℕ R,
      (∀ n, 0 < n → ¬ p ∣ n →
        MvPowerSeries.HasSubst (π n) ∧ (∀ k, MvPowerSeries.constantCoeff (π n k) = 0) ∧
        ∀ k, MvPowerSeries.subst (MvFormalGroup.BigWittLaw.addFam R) (π n k) =
          MvPowerSeries.subst (MvFormalGroup.WittLaw.pairFam (π n)) (MvFormalGroup.WittLaw.addFam p R k)) ∧
      ∀ N : ℕ,
        PowerSeries.trunc N
            (PowerSeries.mk fun k => if k = 0 then (1 : MvPowerSeries ℕ R) else MvPowerSeries.X (k - 1)) =
          PowerSeries.trunc N
            (∏ n ∈ (Finset.range N).filter (fun n => 0 < n ∧ ¬ p ∣ n),
              PowerSeries.mk fun k =>
                if k = 0 then (1 : MvPowerSeries ℕ R)
                else if n ∣ k then
                  MvPowerSeries.subst (π n)
                    (↑(MvPolynomial.map (algebraMap ℤ_[p] R) (MvFormalGroup.ArtinHasse.coord p (k / n - 1))) :
                      MvPowerSeries ℕ R)
                else 0) := by p2m_exact_reverting @_root_.P2MW.S_MvFormalGroup_BigWittLaw_exists_proj_trunc_genSeries_eq_trunc_prod_of_algebra_padicInt.solution
