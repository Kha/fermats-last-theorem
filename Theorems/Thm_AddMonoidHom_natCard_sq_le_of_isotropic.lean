import Mathlib
import P2M.Util
import P2M.Sol.S_AddMonoidHom_natCard_sq_le_of_isotropic

set_option autoImplicit false

theorem AddMonoidHom.natCard_sq_le_of_isotropic
    {V Q : Type*} [AddCommGroup V] [Finite V] [AddCommGroup Q]
    (β : V →+ V →+ Q) (hβ : ∀ v, β v = 0 → v = 0)
    (hQ : ∀ n : ℕ, n ≠ 0 → {x : Q | n • x = 0}.encard ≤ n)
    (K : AddSubgroup V) (hK : ∀ k ∈ K, ∀ k' ∈ K, β k k' = 0) :
    Nat.card K ^ 2 ≤ Nat.card V := by p2m_exact_reverting @_root_.P2MW.S_AddMonoidHom_natCard_sq_le_of_isotropic.solution
