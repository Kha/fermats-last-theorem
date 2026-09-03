import Mathlib
import P2M.Util
import P2M.Sol.S_Matrix_exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe

set_option autoImplicit false

universe u

theorem Matrix.exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe
    (p : ℕ) [Fact p.Prime] {A : Type u} [Ring A] {n : Type} [Fintype n] [DecidableEq n]
    (θ E : A →+* Matrix n n ℚ_[p]) (hθ : Function.Injective θ) (hE : Function.Injective E) (m : ℕ)
    (hθm : ∀ M : Matrix n n ℤ_[p], ∃ a : A, θ a = (p : ℚ_[p]) ^ m • M.map ((↑) : ℤ_[p] → ℚ_[p]))
    (hEint : ∀ a : A, ∃ M : Matrix n n ℤ_[p], E a = M.map ((↑) : ℤ_[p] → ℚ_[p])) :
    ∃ m' : ℕ, ∀ M : Matrix n n ℤ_[p], ∃ a : A, E a = (p : ℚ_[p]) ^ m' • M.map ((↑) : ℤ_[p] → ℚ_[p]) := by p2m_exact_reverting @_root_.P2MW.S_Matrix_exists_forall_exists_eq_pow_smul_map_coe_of_injective_of_forall_exists_eq_map_coe.solution
