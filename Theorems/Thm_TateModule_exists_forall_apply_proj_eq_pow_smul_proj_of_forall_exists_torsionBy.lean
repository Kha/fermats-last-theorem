import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_exists_forall_apply_proj_eq_pow_smul_proj_of_forall_exists_torsionBy

set_option autoImplicit false

theorem TateModule.exists_forall_apply_proj_eq_pow_smul_proj_of_forall_exists_torsionBy
    {p : ℕ} [Fact p.Prime] {M : Type} [AddCommGroup M]
    (hfin : ∀ n : ℕ, (Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ) : Set M).Finite)
    (f : M →+ M) (v : ℕ) (x : TateModule p M)
    (hx : ∀ n : ℕ, ∃ z ∈ Submodule.torsionBy ℤ M ((p ^ (n + v) : ℕ) : ℤ), f z = TateModule.proj p M n x) :
    ∃ w : TateModule p M, ∀ n : ℕ, f (TateModule.proj p M n w) = ((p ^ v : ℕ) : ℤ) • TateModule.proj p M n x := by p2m_exact_reverting @_root_.P2MW.S_TateModule_exists_forall_apply_proj_eq_pow_smul_proj_of_forall_exists_torsionBy.solution
