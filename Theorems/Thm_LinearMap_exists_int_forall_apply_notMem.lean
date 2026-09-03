import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_int_forall_apply_notMem

set_option autoImplicit false

theorem LinearMap.exists_int_forall_apply_notMem
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} {ι : Type*}
    (S : Finset ι) (f : ι → (Fin r → K) →ₗ[K] V) (W : ι → Submodule K V)
    (h : ∀ t ∈ S, ∃ c : Fin r → K, f t c ∉ W t) :
    ∃ c : Fin r → ℤ, ∀ t ∈ S, f t (fun i => (c i : K)) ∉ W t := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_int_forall_apply_notMem.solution
