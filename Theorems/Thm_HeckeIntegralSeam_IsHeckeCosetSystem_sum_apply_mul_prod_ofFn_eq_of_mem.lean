import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_HeckeIntegralSeam_IsHeckeCosetSystem_sum_apply_mul_prod_ofFn_eq_of_mem

set_option autoImplicit false

theorem HeckeIntegralSeam.IsHeckeCosetSystem.sum_apply_mul_prod_ofFn_eq_of_mem
    {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι₀ : Type*} [Fintype ι₀] {reps : ι₀ → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps)
    {M : Type*} [AddCommMonoid M] (φ : G → M) (hφ : ∀ x : G, ∀ u ∈ U, φ (x * u) = φ x)
    (k : ℕ) (x u : G) (hu : u ∈ U) :
    ∑ ι : Fin k → ι₀, φ (x * u * (List.ofFn fun m => reps (ι m)).prod) =
      ∑ ι : Fin k → ι₀, φ (x * (List.ofFn fun m => reps (ι m)).prod) := by p2m_exact_reverting @_root_.P2MW.S_HeckeIntegralSeam_IsHeckeCosetSystem_sum_apply_mul_prod_ofFn_eq_of_mem.solution
