import Mathlib
import P2M.Util
import P2M.Sol.S_PadicInt_addMonoidHom_map_smul_of_free

set_option autoImplicit false

universe u v

theorem PadicInt.addMonoidHom_map_smul_of_free
    (p : ℕ) [Fact p.Prime] {N : Type u} {M : Type v}
    [AddCommGroup N] [Module ℤ_[p] N] [Module.Free ℤ_[p] N]
    [AddCommGroup M] [Module ℤ_[p] M] [Module.Free ℤ_[p] M]
    (f : N →+ M) (c : ℤ_[p]) (x : N) :
    f (c • x) = c • f x := by p2m_exact_reverting @_root_.P2MW.S_PadicInt_addMonoidHom_map_smul_of_free.solution
