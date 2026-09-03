import Mathlib
import P2M.Util
import P2M.Sol.S_CerednikDrinfeld_exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic

set_option autoImplicit false

theorem CerednikDrinfeld.exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic
    {r : ℕ} [Fact r.Prime]
    (vdet : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ)
    (hvdet : ∀ (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r]) (n : ℤ), vdet g = Multiplicative.ofAdd n ↔
      ∃ u : ℤ_[r]ˣ, (Matrix.GeneralLinearGroup.det g : ℚ_[r]) = algebraMap ℤ_[r] ℚ_[r] (u : ℤ_[r]) * (algebraMap ℤ_[r] ℚ_[r] ((r : ℕ) : ℤ_[r])) ^ n)
    (ν : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r] →* Multiplicative ℤ) :
    ∃ c : ℤ, ∀ g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r], ν g = (vdet g) ^ c := by p2m_exact_reverting @_root_.P2MW.S_CerednikDrinfeld_exists_forall_apply_eq_zpow_of_monoidHom_generalLinearGroup_padic.solution
