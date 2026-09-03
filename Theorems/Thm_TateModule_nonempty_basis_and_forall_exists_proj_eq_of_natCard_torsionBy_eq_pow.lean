import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_nonempty_basis_and_forall_exists_proj_eq_of_natCard_torsionBy_eq_pow

set_option autoImplicit false

theorem TateModule.nonempty_basis_and_forall_exists_proj_eq_of_natCard_torsionBy_eq_pow
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r) :
    Nonempty (Module.Basis (Fin r) ℤ_[p] (TateModule p M)) ∧
    ∀ (n : ℕ) (m : M), ((p ^ n : ℕ) : ℤ) • m = 0 → ∃ x : TateModule p M, (x : ℕ → M) n = m := by p2m_exact_reverting @_root_.P2MW.S_TateModule_nonempty_basis_and_forall_exists_proj_eq_of_natCard_torsionBy_eq_pow.solution
