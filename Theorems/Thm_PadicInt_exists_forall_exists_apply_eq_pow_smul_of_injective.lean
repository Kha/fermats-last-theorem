import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_exists_forall_exists_apply_eq_pow_smul_of_injective

set_option autoImplicit false

p2m_open "scoped PadicInt~addMonoidHom_map_smul_of_free"

theorem PadicInt.exists_forall_exists_apply_eq_pow_smul_of_injective
    (p : ℕ) [Fact p.Prime] {n : ℕ} (f : (Fin n → ℤ_[p]) →+ (Fin n → ℤ_[p])) (hf : Function.Injective f) :
    ∃ N : ℕ, ∀ v : Fin n → ℤ_[p], ∃ w : Fin n → ℤ_[p], f w = (p : ℤ_[p]) ^ N • v := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_exists_forall_exists_apply_eq_pow_smul_of_injective.solution
