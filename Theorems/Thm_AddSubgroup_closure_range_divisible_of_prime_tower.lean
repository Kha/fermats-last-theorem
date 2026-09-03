import Mathlib
import P2M.Util
import P2M.Sol.S_AddSubgroup_closure_range_divisible_of_prime_tower

set_option autoImplicit false

theorem AddSubgroup.closure_range_divisible_of_prime_tower
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (p : ℕ) (hp : p.Prime) (f : ℕ → M)
    (htrans : ∀ n, p • f (n + 1) = f n) (htors : ∀ n, p ^ n • f n = 0)
    (I : Set R) (hkill : ∀ t ∈ I, ∀ n, t • f n = 0) (hne : ∃ n, f n ≠ 0) :
    AddSubgroup.closure (Set.range f) ≠ ⊥ ∧
      (∀ z ∈ AddSubgroup.closure (Set.range f), ∀ k : ℕ, 0 < k →
        ∃ z' ∈ AddSubgroup.closure (Set.range f), k • z' = z) ∧
      (∀ t ∈ I, ∀ z ∈ AddSubgroup.closure (Set.range f), t • z = 0) := by p2m_exact_reverting @_root_.P2MW.S_AddSubgroup_closure_range_divisible_of_prime_tower.solution
