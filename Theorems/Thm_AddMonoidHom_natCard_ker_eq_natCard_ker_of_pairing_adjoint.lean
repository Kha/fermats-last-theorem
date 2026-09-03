import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint

set_option autoImplicit false

theorem AddMonoidHom.natCard_ker_eq_natCard_ker_of_pairing_adjoint
    {P : Type*} [AddCommGroup P] [Finite P] {K : Type*} [Field K]
    (e : P → P → Kˣ)
    (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y) (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
    (hleft : ∀ x, (∀ y, e x y = 1) → x = 0) (hright : ∀ y, (∀ x, e x y = 1) → y = 0)
    (hsurj : ∀ χ : Multiplicative P →* Kˣ, ∃ y, ∀ x, e x y = χ (Multiplicative.ofAdd x))
    (T T' : P →+ P) (hadj : ∀ x y, e (T x) y = e x (T' y)) :
    Nat.card (T.ker) = Nat.card (T'.ker) := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint.solution
