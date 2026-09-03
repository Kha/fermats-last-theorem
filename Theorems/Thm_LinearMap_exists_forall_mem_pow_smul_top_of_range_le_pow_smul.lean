import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_mem_pow_smul_top_of_range_le_pow_smul
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ c : ℕ, ∀ (n : ℕ) (g : M →ₗ[B] N),
      LinearMap.range g ≤ I ^ (n + c) • (⊤ : Submodule B N) →
      g ∈ I ^ n • (⊤ : Submodule B (M →ₗ[B] N)) := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul.solution
