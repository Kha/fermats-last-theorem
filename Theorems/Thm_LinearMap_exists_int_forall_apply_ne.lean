import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_int_forall_apply_ne

set_option autoImplicit false

theorem LinearMap.exists_int_forall_apply_ne {K : Type*} [Field K] [CharZero K] {r : ℕ} {ι : Type*}
    (S : Finset ι) (f : ι → (Fin r → K) →ₗ[K] K) (a : ι → K) (hf : ∀ j ∈ S, f j ≠ 0) :
    ∃ c : Fin r → ℤ, ∀ j ∈ S, f j (fun i => (c i : K)) ≠ a j := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_int_forall_apply_ne.solution
