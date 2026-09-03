import Mathlib
import P2M.Util
import P2M.Sol.S_TensorProduct_exists_pow_smul_eq_one_tmul

open scoped TensorProduct

theorem TensorProduct.exists_pow_smul_eq_one_tmul (q : ℕ) [Fact q.Prime]
    (T : Type) [AddCommGroup T] [Module ℤ_[q] T] (w : ℚ_[q] ⊗[ℤ_[q]] T) :
    ∃ (k : ℕ) (t : T), ((q : ℚ_[q]) ^ k) • w = (1 : ℚ_[q]) ⊗ₜ[ℤ_[q]] t := by p2m_exact_reverting @_root_.P2MW.S_TensorProduct_exists_pow_smul_eq_one_tmul.solution
