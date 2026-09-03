import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Ker
import P2M.Util
import P2M.Sol.S_Submodule_mem_of_forall_prime_exists_smul_mem

theorem Submodule.mem_of_forall_prime_exists_smul_mem
    {V : Type*} [AddCommGroup V] (M : Submodule ℤ V) (x : V)
    (h : ∀ ℓ : ℕ, ℓ.Prime → ∃ s : ℤ, ¬ (ℓ : ℤ) ∣ s ∧ s • x ∈ M) : x ∈ M := by p2m_exact_reverting @_root_.P2MW.S_Submodule_mem_of_forall_prime_exists_smul_mem.solution
