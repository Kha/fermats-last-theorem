import Mathlib
import Definitions.Def_DualIsogenyAPI
import P2M.Util
import P2M.Sol.S_AddMonoidHom_IsDualPair_forall_q_zsmul_eq_zero_of_isCoprime

theorem AddMonoidHom.IsDualPair.forall_q_zsmul_eq_zero_of_isCoprime
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {φ : A →+ B} {ψ : B →+ A} {n : ℤ}
    (hdual : AddMonoidHom.IsDualPair φ ψ n) (q : ℕ)
    (hcop : IsCoprime n (q : ℤ))
    (hA : ∀ a : A, (q : ℤ) • a = 0 → a = 0) :
    ∀ b : B, (q : ℤ) • b = 0 → b = 0 := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_IsDualPair_forall_q_zsmul_eq_zero_of_isCoprime.solution
