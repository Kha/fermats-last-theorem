import Mathlib
import P2M.Util
import P2M.Sol.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp

set_option autoImplicit false

universe u v w

theorem LinearMap.exists_forall_exists_mkQ_comp_eq_factor_comp
    {B : Type u} [CommRing B] [IsNoetherianRing B] (I : Ideal B)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    {N : Type w} [AddCommGroup N] [Module B N] [Module.Finite B N] :
    ∃ c : ℕ, ∀ (n : ℕ) (f : M →ₗ[B] N ⧸ (I ^ (n + c) • (⊤ : Submodule B N))),
      ∃ g : M →ₗ[B] N,
        (I ^ n • (⊤ : Submodule B N)).mkQ ∘ₗ g =
          Submodule.factor (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n c))) ∘ₗ f := by p2m_exact_reverting @_root_.P2MW.S_LinearMap_exists_forall_exists_mkQ_comp_eq_factor_comp.solution
