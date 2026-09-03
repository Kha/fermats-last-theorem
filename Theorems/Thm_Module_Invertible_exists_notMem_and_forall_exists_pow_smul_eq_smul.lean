import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Invertible_exists_notMem_and_forall_exists_pow_smul_eq_smul

set_option autoImplicit false

universe u v

theorem Module.Invertible.exists_notMem_and_forall_exists_pow_smul_eq_smul
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] [Module.Invertible R M]
    (p : Ideal R) [p.IsPrime] :
    ∃ t : R, t ∉ p ∧ ∃ m₀ : M, ∀ m : M, ∃ (n : ℕ) (r : R), t ^ n • m = r • m₀ := by p2m_exact_reverting @_root_.P2MW.S_Module_Invertible_exists_notMem_and_forall_exists_pow_smul_eq_smul.solution
