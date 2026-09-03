import Mathlib
import P2M.Util
import P2M.Sol.S_WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range

set_option autoImplicit false

open scoped PadicInt

theorem WittVector.exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range
    (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    ∃ c : ℤ_[p] →+* WittVector p K, Function.Injective c ∧
      ∀ w : WittVector p K, WittVector.frobenius w = w ↔ w ∈ Set.range c := by p2m_exact_reverting @_root_.P2MW.S_WittVector_exists_ringHom_padicInt_injective_frobenius_eq_iff_mem_range.solution
