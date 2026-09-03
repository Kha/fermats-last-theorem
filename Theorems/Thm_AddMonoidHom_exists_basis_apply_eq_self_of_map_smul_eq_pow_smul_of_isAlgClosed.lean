import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed

set_option autoImplicit false

universe u v

theorem AddMonoidHom.exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed
    (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [IsAlgClosed k] [CharP k p]
    (V : Type v) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (φ : V →+ V) (hφ : ∀ (c : k) (x : V), φ (c • x) = c ^ p • φ x)
    (hinj : Function.Injective φ) :
    ∃ b : Module.Basis (Fin (Module.finrank k V)) k V, ∀ i, φ (b i) = b i := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_exists_basis_apply_eq_self_of_map_smul_eq_pow_smul_of_isAlgClosed.solution
