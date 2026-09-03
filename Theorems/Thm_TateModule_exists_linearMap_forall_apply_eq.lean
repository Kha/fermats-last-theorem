import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_exists_linearMap_forall_apply_eq

set_option autoImplicit false

theorem TateModule.exists_linearMap_forall_apply_eq
    (p : ℕ) [Fact p.Prime] (M M' : Type) [AddCommGroup M] [AddCommGroup M'] (φ : M →+ M') :
    ∃ T : TateModule p M →ₗ[ℤ_[p]] TateModule p M',
      ∀ (x : TateModule p M) (n : ℕ), ((T x : TateModule p M') : ℕ → M') n = φ ((x : ℕ → M) n) := by p2m_exact_reverting @_root_.P2MW.S_TateModule_exists_linearMap_forall_apply_eq.solution
