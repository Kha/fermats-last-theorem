import Mathlib
import P2M.Util
import P2M.Sol.S_MvPolynomial_forall_apply_eq_apply_smul_of_forall_X_of_eq_act

set_option autoImplicit false

open MvPolynomial

theorem MvPolynomial.forall_apply_eq_apply_smul_of_forall_X_of_eq_act
    {σ : Type*} {E : Type*} {M : Type*} {R : Type*}
    [AddCommGroup M] [Module (MvPolynomial σ ℤ) M] [AddCommGroup R]
    (K : E → Prop) (mul : E → E → E) (act : MvPolynomial σ ℤ → E → E)
    (hKact : ∀ (t : MvPolynomial σ ℤ) (x : E), K x → K (act t x))
    (hact_mul : ∀ (s t : MvPolynomial σ ℤ) (x : E), K x → act (s * t) x = act t (act s x))
    (hact_add : ∀ (s t : MvPolynomial σ ℤ) (x : E), K x → act (s + t) x = mul (act s x) (act t x))
    (hact_one : ∀ x : E, K x → act 1 x = x)
    (τ : {x : E // K x} → (M →+ R))
    (hτ : ∀ x y z : {x : E // K x}, z.1 = mul x.1 y.1 → τ z = τ x + τ y)
    (hX : ∀ (n : σ) (x y : {x : E // K x}), y.1 = act (X n) x.1 → ∀ g : M, τ y g = τ x ((X n : MvPolynomial σ ℤ) • g)) :
    ∀ (t : MvPolynomial σ ℤ) (x y : {x : E // K x}), y.1 = act t x.1 → ∀ g : M, τ y g = τ x (t • g) := by p2m_exact_reverting @_root_.P2MW.S_MvPolynomial_forall_apply_eq_apply_smul_of_forall_X_of_eq_act.solution
