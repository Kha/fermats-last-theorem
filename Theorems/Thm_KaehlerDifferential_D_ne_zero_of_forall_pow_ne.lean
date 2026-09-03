import Mathlib
import P2M.Util
import P2M.Sol.S_KaehlerDifferential_D_ne_zero_of_forall_pow_ne

set_option autoImplicit false

universe u

theorem KaehlerDifferential.D_ne_zero_of_forall_pow_ne
    {k : Type u} [Field k] (p : ℕ) (hp : p.Prime) [ExpChar k p]
    (c : k) (hc : ∀ b : k, b ^ p ≠ c) :
    KaehlerDifferential.D (⊥ : Subfield k) k c ≠ 0 := by p2m_exact_reverting @_root_.P2MW.S_KaehlerDifferential_D_ne_zero_of_forall_pow_ne.solution
