import Mathlib
import P2M.Util
import P2M.Sol.S_Module_Flat_exists_mem_smul_top_map_eq_of_ker_baseChange_le_range

set_option autoImplicit false

universe u

theorem Module.Flat.exists_mem_smul_top_map_eq_of_ker_baseChange_le_range
    {R : Type u} [CommRing R] (k : Type u) [Field k] [Algebra R k] (hk : Function.Surjective (algebraMap R k))
    (I : Ideal R) (hI : I * RingHom.ker (algebraMap R k) = ⊥)
    {C₀ C₁ C₂ : Type u} [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
    [Module.Flat R C₁] [Module.Flat R C₂]
    (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂)
    (hex : LinearMap.ker (d₁.baseChange k) ≤ LinearMap.range (d₀.baseChange k))
    (c : C₁) (hc : c ∈ I • (⊤ : Submodule R C₁)) (hdc : d₁ c = 0) :
    ∃ b ∈ I • (⊤ : Submodule R C₀), d₀ b = c := by p2m_exact_reverting @_root_.P2MW.S_Module_Flat_exists_mem_smul_top_map_eq_of_ker_baseChange_le_range.solution
