import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_exists_forall_apply_eq_pow_smul_imp_exists_eq_smul_of_injective

set_option autoImplicit false

theorem PadicInt.exists_forall_apply_eq_pow_smul_imp_exists_eq_smul_of_injective
    (p : ℕ) [Fact p.Prime] {n : ℕ}
    (f : (Fin n → ℤ_[p]) →+ (Fin n → ℤ_[p])) (hf : Function.Injective f) :
    ∃ M : ℕ, ∀ (w y : Fin n → ℤ_[p]), f w = ((p : ℤ_[p]) ^ M) • y →
      ∃ v : Fin n → ℤ_[p], w = (p : ℤ_[p]) • v := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_forall_apply_eq_pow_smul_imp_exists_eq_smul_of_injective.solution
