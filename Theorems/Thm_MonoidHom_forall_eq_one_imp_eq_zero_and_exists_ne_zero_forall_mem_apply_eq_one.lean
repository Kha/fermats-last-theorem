import Mathlib
import P2M.Util
import P2M.Sol.S_MonoidHom_forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one

set_option autoImplicit false

theorem MonoidHom.forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] [Finite M] (hM : ∀ m : M, p • m = 0)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] :
    (∀ m : M, (∀ χ : Multiplicative M →* Lˣ, χ (Multiplicative.ofAdd m) = 1) → m = 0) ∧
    (∀ K : Subgroup (Multiplicative M →* Lˣ), K ≠ ⊤ →
      ∃ m : M, m ≠ 0 ∧ ∀ χ ∈ K, χ (Multiplicative.ofAdd m) = 1) := by p2m_exact_reverting @_root_.P2MW.S_MonoidHom_forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one.solution
