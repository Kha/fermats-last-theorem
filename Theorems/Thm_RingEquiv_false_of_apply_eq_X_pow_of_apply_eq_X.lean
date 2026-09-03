import Mathlib
import P2M.Util
import P2M.Sol.S_RingEquiv_false_of_apply_eq_X_pow_of_apply_eq_X
set_option autoImplicit false
universe u v
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem RingEquiv.false_of_apply_eq_X_pow_of_apply_eq_X
    (p : ℕ) (hp : 2 ≤ p) (k : Type v) [CommRing k] [Nontrivial k]
    (R : Type u) [CommRing R] (e₀ e₁ : R ≃+* Polynomial k) (a b : R)
    (h₀a : e₀ a = Polynomial.X) (h₀b : e₀ b = Polynomial.X ^ p)
    (h₁b : e₁ b = Polynomial.X) (h₁a : e₁ a = Polynomial.X ^ p) : False := by p2m_exact_reverting @_root_.P2MW.S_RingEquiv_false_of_apply_eq_X_pow_of_apply_eq_X.solution
