import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import P2M.Util
import P2M.Sol.S_CuspidalType_IsCuspidalOfType_forall_apply_pow_eq_one_and_exists_apply_sq_ne_one

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.IsCuspidalOfType.forall_apply_pow_eq_one_and_exists_apply_sq_ne_one
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (θ : (GaloisField q 2)ˣ →* Kˣ) (ρ : Representation K (GL2 q) V)
    (h : IsCuspidalOfType θ ρ) :
    (∀ α : (GaloisField q 2)ˣ, θ (α ^ (q + 1)) = 1) ∧
    (((q + 1 : ℕ) : K) ≠ 0 → ∃ α : (GaloisField q 2)ˣ, (θ α) ^ 2 ≠ 1) := by p2m_exact_reverting @_root_.P2MW.S_CuspidalType_IsCuspidalOfType_forall_apply_pow_eq_one_and_exists_apply_sq_ne_one.solution
