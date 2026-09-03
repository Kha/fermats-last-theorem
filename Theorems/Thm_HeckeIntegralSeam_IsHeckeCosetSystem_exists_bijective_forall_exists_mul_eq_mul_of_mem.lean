import Definitions.Def_LocalLanglands_HeckeCosetSystem
import P2M.Util
import P2M.Sol.S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem

set_option autoImplicit false

theorem HeckeIntegralSeam.IsHeckeCosetSystem.exists_bijective_forall_exists_mul_eq_mul_of_mem
    {G : Type*} [Group G] {U : Subgroup G} {g : G} {ι₀ : Type*} {reps : ι₀ → G}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem U g reps) (u : G) (hu : u ∈ U) :
    ∃ π : ι₀ → ι₀, Function.Bijective π ∧
      ∀ i : ι₀, ∃ u' ∈ U, u * reps i = reps (π i) * u' := by p2m_exact_reverting @_root_.P2MW.S_HeckeIntegralSeam_IsHeckeCosetSystem_exists_bijective_forall_exists_mul_eq_mul_of_mem.solution
