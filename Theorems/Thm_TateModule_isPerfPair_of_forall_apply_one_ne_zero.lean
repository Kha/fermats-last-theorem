import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_isPerfPair_of_forall_apply_one_ne_zero

set_option autoImplicit false

theorem TateModule.isPerfPair_of_forall_apply_one_ne_zero
    (p : ℕ) [Fact p.Prime] (M : Type) [AddCommGroup M] (r : ℕ)
    (hcard : ∀ n : ℕ, Nat.card (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) = (p ^ n) ^ r)
    (e : TateModule p M →ₗ[ℤ_[p]] TateModule p M →ₗ[ℤ_[p]] ℤ_[p])
    (hleft : ∀ a : TateModule p M, (a : ℕ → M) 1 ≠ 0 → ∃ b : TateModule p M, ¬ (p : ℤ_[p]) ∣ e a b)
    (hright : ∀ b : TateModule p M, (b : ℕ → M) 1 ≠ 0 → ∃ a : TateModule p M, ¬ (p : ℤ_[p]) ∣ e a b) :
    e.IsPerfPair := by p2m_exact_reverting @_root_.P2MW.S_TateModule_isPerfPair_of_forall_apply_one_ne_zero.solution
