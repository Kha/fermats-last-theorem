import Mathlib
import Definitions.Def_PadicAlgCl_CyclotomicTower
import P2M.Util
import P2M.Sol.S_PadicAlgCl_finrank_sup_cyclotomicTower_of_forall_norm_eq_zpow

set_option autoImplicit false

theorem PadicAlgCl.finrank_sup_cyclotomicTower_of_forall_norm_eq_zpow (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (hK : ∀ x ∈ K, x ≠ 0 → ∃ k : ℤ, ‖x‖ = (p : ℝ) ^ k) (n : ℕ) (hn : 0 < n) :
    Module.finrank ℚ_[p] ↥(K ⊔ PadicAlgCl.cyclotomicTower p n) =
      Module.finrank ℚ_[p] K * ((p - 1) * p ^ (n - 1)) := by p2m_exact_reverting @_root_.P2MW.S_PadicAlgCl_finrank_sup_cyclotomicTower_of_forall_norm_eq_zpow.solution
