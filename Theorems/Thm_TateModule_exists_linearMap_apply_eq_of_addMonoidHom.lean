import Mathlib
import Definitions.Def_EllipticCurve_TateModule
import P2M.Util
import P2M.Sol.S_TateModule_exists_linearMap_apply_eq_of_addMonoidHom

set_option autoImplicit false

theorem TateModule.exists_linearMap_apply_eq_of_addMonoidHom
    (p : ℕ) [Fact p.Prime] {M M' : Type} [AddCommGroup M] [AddCommGroup M'] (f : M →+ M') :
    ∃ e : TateModule p M →ₗ[ℤ_[p]] TateModule p M',
      (∀ (x : TateModule p M) (n : ℕ), ((e x : TateModule p M') : ℕ → M') n = f ((x : ℕ → M) n)) ∧
      (Function.Injective f → Function.Injective e) := by p2m_exact_reverting @_root_.P2MW.S_TateModule_exists_linearMap_apply_eq_of_addMonoidHom.solution
