import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed

set_option autoImplicit false

universe u v

theorem AddMonoidHom.exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (M : Type v) [AddCommGroup M] [Module (WittVector p k) M]
    [Module.Free (WittVector p k) M] [Module.Finite (WittVector p k) M]
    (U : M →+ M) (hU : ∀ (w : WittVector p k) (x : M), U (w • x) = WittVector.frobenius w • U x)
    (hbij : Function.Bijective U) :
    ∃ b : Module.Basis (Fin (Module.finrank (WittVector p k) M)) (WittVector p k) M,
      ∀ i, U (b i) = b i := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_frobenius_smul_of_isAlgClosed.solution
